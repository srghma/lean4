// Lean compiler output
// Module: Lean.Meta.Sym.Util
// Imports: Lean.Meta.Sym.SymM Lean.Meta.Transform Init.Grind.Util Lean.Meta.WHNF Lean.Meta.AppBuilder Lean.Util.ForEachExpr
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_size, lean_array_push, lean_array_set, lean_array_size, lean_array_uget,
    lean_array_uget_borrowed, lean_array_uset, lean_expr_eqv, lean_expr_instantiate_rev,
    lean_find_expr, lean_mk_array, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_ptr_addr, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_string_append, lean_string_dec_eq, lean_uint64_lor, lean_uint64_shift_left,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_land, lean_usize_mul,
    lean_usize_of_nat, lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Grind::Util::{
    initialize_Init_Grind_Util, runtime_initialize_Init_Grind_Util,
};
use crate::r#gen::Init::Prelude::{l_Lean_Name_append, l_Lean_maxRecDepthErrorMessage};
use crate::r#gen::Init::System::CancelToken::l_IO_CancelToken_isSet;
use crate::r#gen::Init::System::ST::{l_ST_Prim_Ref_get___boxed, l_ST_Prim_mkRef___boxed};
use crate::r#gen::Init::Util::l_ptrEqList___redArg;
use crate::r#gen::Lean::CoreM::l_Lean_Core_checkSystem;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Exception::l_Lean_interruptExceptionId;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_const___override, l_Lean_Expr_forallE___override, l_Lean_Expr_getAppFn,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hasMVar, l_Lean_Expr_hash, l_Lean_Expr_isConst,
    l_Lean_Expr_isProj___boxed, l_Lean_Expr_lam___override, l_Lean_Expr_letE___override,
    l_Lean_Expr_mdata___override, l_Lean_Expr_mvarId_x21, l_Lean_Expr_proj___override,
    l_Lean_Expr_sort___override, l_Lean_ExprStructEq_beq, l_Lean_ExprStructEq_hash,
    l_Lean_instBEqBinderInfo_beq, l_Lean_instBEqFVarId_beq, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableFVarId_hash, l_Lean_instHashableMVarId_hash, l_Lean_mkAppN,
};
use crate::r#gen::Lean::Level::{l_Lean_Level_isAlreadyNormalizedCheap, l_Lean_Level_normalize};
use crate::r#gen::Lean::LocalContext::l_Lean_LocalDecl_fvarId;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_indentExpr,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkProjection,
    runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp, l_Lean_MVarId_getDecl,
    l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_TransparencyMode_toUInt64, l_Lean_Meta_mkForallFVars,
    l_Lean_Meta_mkFreshExprMVarAt, l_Lean_Meta_mkLambdaFVars, l_Lean_Meta_mkLetFVars,
};
use crate::r#gen::Lean::Meta::FunInfo::l_Lean_Meta_getFunInfoNArgs;
use crate::r#gen::Lean::Meta::Sym::AlphaShareCommon::{
    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq,
    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1;
use crate::r#gen::Lean::Meta::Sym::SymM::{
    initialize_Lean_Meta_Sym_SymM, l_Lean_Meta_Sym_shareCommon___redArg,
    runtime_initialize_Lean_Meta_Sym_SymM,
};
use crate::r#gen::Lean::Meta::Transform::{
    initialize_Lean_Meta_Transform, runtime_initialize_Lean_Meta_Transform,
};
use crate::r#gen::Lean::Meta::WHNF::{
    initialize_Lean_Meta_WHNF, l_Lean_Meta_unfoldDefinition_x3f, runtime_initialize_Lean_Meta_WHNF,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::ProjFns::l_Lean_Environment_isProjectionFn;
use crate::r#gen::Lean::ReducibilityAttrs::lean_get_reducibility_status;
use crate::r#gen::Lean::Structure::l_Lean_getStructureInfo_x3f;
use crate::r#gen::Lean::Util::ForEachExpr::{
    initialize_Lean_Util_ForEachExpr, runtime_initialize_Lean_Util_ForEachExpr,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
pub static l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__0_value:
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
static mut l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__1_value:
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
    m_data: [71, 114, 105, 110, 100, 0],
};
static mut l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__2_value:
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
    m_data: [69, 113, 77, 97, 116, 99, 104, 0],
};
static mut l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__2_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__3_value_aux_0:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__3_value_aux_1:
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
            l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__3_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__3_value:
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
            l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__3_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        1625593685836349312 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_unfoldReducibleStep___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 2,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_Meta_Sym_unfoldReducibleStep___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7310567555909517314 as *mut crate::leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value) as *mut crate::leanh::LeanObject,273128857561458264 as *mut crate::leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 114, 97, 110, 115, 102, 111, 114, 109, 0]};
static mut l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_unfoldReducible___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Sym_unfoldReducible___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_unfoldReducible___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_unfoldReducible___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_unfoldReducible___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Sym_unfoldReducibleStep___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_unfoldReducible___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_unfoldReducible___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2_value:
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
static mut l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_foldProjs___lam__0___closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [115, 121, 109, 0],
    };
static mut l_Lean_Meta_Sym_foldProjs___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_foldProjs___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_foldProjs___lam__0___closed__1_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [105, 115, 115, 117, 101, 115, 0],
    };
static mut l_Lean_Meta_Sym_foldProjs___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_foldProjs___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_foldProjs___lam__0___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_foldProjs___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16563840882919605222 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_foldProjs___lam__0___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Sym_foldProjs___lam__0___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_foldProjs___lam__0___closed__1_value)
                as *mut crate::leanh::LeanObject,
            13379912757096045311 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_foldProjs___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_foldProjs___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_foldProjs___lam__0___closed__3_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [116, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Meta_Sym_foldProjs___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_foldProjs___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_foldProjs___lam__0___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_foldProjs___lam__0___closed__3_value)
                as *mut crate::leanh::LeanObject,
            14231257465488249300 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_foldProjs___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_foldProjs___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_foldProjs___lam__0___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_foldProjs___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_foldProjs___lam__0___closed__6_value: crate::leanh::LeanStringObject<
    45,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 45,
    m_capacity: 45,
    m_length: 44,
    m_data: [
        102, 111, 117, 110, 100, 32, 96, 69, 120, 112, 114, 46, 112, 114, 111, 106, 96, 32, 119,
        105, 116, 104, 32, 105, 110, 118, 97, 108, 105, 100, 32, 102, 105, 101, 108, 100, 32, 105,
        110, 100, 101, 120, 32, 96, 0,
    ],
};
static mut l_Lean_Meta_Sym_foldProjs___lam__0___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_foldProjs___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_foldProjs___lam__0___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_foldProjs___lam__0___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_foldProjs___lam__0___closed__8_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Sym_foldProjs___lam__0___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_foldProjs___lam__0___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_foldProjs___lam__0___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_foldProjs___lam__0___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_foldProjs___lam__0___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_foldProjs___lam__0___closed__10: u64 = 0;
pub static l_Lean_Meta_Sym_foldProjs___lam__0___closed__11_value: crate::leanh::LeanStringObject<
    24,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        102, 111, 117, 110, 100, 32, 96, 69, 120, 112, 114, 46, 112, 114, 111, 106, 96, 32, 98,
        117, 116, 32, 96, 0,
    ],
};
static mut l_Lean_Meta_Sym_foldProjs___lam__0___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_foldProjs___lam__0___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_foldProjs___lam__0___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_foldProjs___lam__0___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_foldProjs___lam__0___closed__13_value: crate::leanh::LeanStringObject<
    29,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        96, 32, 105, 115, 32, 110, 111, 116, 32, 109, 97, 114, 107, 101, 100, 32, 97, 115, 32, 115,
        116, 114, 117, 99, 116, 117, 114, 101, 0,
    ],
};
static mut l_Lean_Meta_Sym_foldProjs___lam__0___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_foldProjs___lam__0___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_foldProjs___lam__0___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_foldProjs___lam__0___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_foldProjs___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Expr_isProj___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_foldProjs___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_foldProjs___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_foldProjs___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Sym_foldProjs___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_foldProjs___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_foldProjs___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_foldProjs___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Sym_foldProjs___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_foldProjs___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_foldProjs___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__0_value: crate::leanh::LeanStringObject<42> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [116, 101, 114, 109, 32, 105, 115, 32, 110, 111, 116, 32, 105, 110, 32, 116, 104, 101, 32, 109, 97, 120, 105, 109, 97, 108, 108, 121, 32, 115, 104, 97, 114, 101, 100, 32, 116, 97, 98, 108, 101, 0]};
static mut l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__3_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [93, 32, 0]};
static mut l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_normalizeLevels___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Sym_normalizeLevels___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_normalizeLevels___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_normalizeLevels___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_normalizeLevels___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Sym_normalizeLevels___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_normalizeLevels___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_normalizeLevels___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget(
    mut v_declName_4528_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: u8 = 0;
    v___x_4529_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__3;
    v___x_4530_ = lean_name_eq(v_declName_4528_, v___x_4529_);
    return v___x_4530_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___boxed(
    mut v_declName_4531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4532_: u8 = 0;
    let mut v_r_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4532_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget(v_declName_4531_);
    crate::leanh::lean_dec(v_declName_4531_);
    v_r_4533_ = crate::leanh::lean_box((v_res_4532_) as usize);
    return v_r_4533_;
}
pub unsafe fn l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0_spec__0___redArg(
    mut v_declName_4534_: *mut crate::leanh::LeanObject,
    mut v___y_4535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: u8 = 0;
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4537_ = lean_st_ref_get(v___y_4535_);
    v_env_4538_ = crate::leanh::lean_ctor_get(v___x_4537_, 0);
    crate::leanh::lean_inc_ref(v_env_4538_);
    crate::leanh::lean_dec(v___x_4537_);
    v___x_4539_ = lean_get_reducibility_status(v_env_4538_, v_declName_4534_);
    v___x_4540_ = crate::leanh::lean_box((v___x_4539_) as usize);
    v___x_4541_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4541_, 0, v___x_4540_);
    return v___x_4541_;
}
pub unsafe fn l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0_spec__0___redArg___boxed(
    mut v_declName_4542_: *mut crate::leanh::LeanObject,
    mut v___y_4543_: *mut crate::leanh::LeanObject,
    mut v___y_4544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4545_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0_spec__0___redArg(v_declName_4542_, v___y_4543_);
    crate::leanh::lean_dec(v___y_4543_);
    return v_res_4545_;
}
pub unsafe fn l_Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0(
    mut v_declName_4546_: *mut crate::leanh::LeanObject,
    mut v___y_4547_: *mut crate::leanh::LeanObject,
    mut v___y_4548_: *mut crate::leanh::LeanObject,
    mut v___y_4549_: *mut crate::leanh::LeanObject,
    mut v___y_4550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4556_: u8 = 0;
    let mut v___x_4557_: u8 = 0;
    let mut v___x_4558_: u8 = 0;
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: u8 = 0;
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4568_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4552_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0_spec__0___redArg(v_declName_4546_, v___y_4550_);
                v_a_4553_ = crate::leanh::lean_ctor_get(v___x_4552_, 0);
                v_isSharedCheck_4568_ = (!crate::leanh::lean_is_exclusive(v___x_4552_)) as u8;
                if v_isSharedCheck_4568_ == 0 {
                    v___x_4555_ = v___x_4552_;
                    v_isShared_4556_ = v_isSharedCheck_4568_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4553_);
                    crate::leanh::lean_dec(v___x_4552_);
                    v___x_4555_ = crate::leanh::lean_box(0);
                    v_isShared_4556_ = v_isSharedCheck_4568_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4557_ = (crate::leanh::lean_unbox(v_a_4553_) as u8);
                crate::leanh::lean_dec(v_a_4553_);
                if v___x_4557_ == 0 {
                    v___x_4558_ = 1;
                    v___x_4559_ = crate::leanh::lean_box((v___x_4558_) as usize);
                    if v_isShared_4556_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4555_, 0, v___x_4559_);
                        v___x_4561_ = v___x_4555_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4562_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4562_, 0, v___x_4559_);
                        v___x_4561_ = v_reuseFailAlloc_4562_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4563_ = 0;
                    v___x_4564_ = crate::leanh::lean_box((v___x_4563_) as usize);
                    if v_isShared_4556_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4555_, 0, v___x_4564_);
                        v___x_4566_ = v___x_4555_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4567_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4567_, 0, v___x_4564_);
                        v___x_4566_ = v_reuseFailAlloc_4567_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4561_;
            }
            3 => {
                return v___x_4566_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0___boxed(
    mut v_declName_4569_: *mut crate::leanh::LeanObject,
    mut v___y_4570_: *mut crate::leanh::LeanObject,
    mut v___y_4571_: *mut crate::leanh::LeanObject,
    mut v___y_4572_: *mut crate::leanh::LeanObject,
    mut v___y_4573_: *mut crate::leanh::LeanObject,
    mut v___y_4574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4575_ = l_Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0(
        v_declName_4569_,
        v___y_4570_,
        v___y_4571_,
        v___y_4572_,
        v___y_4573_,
    );
    crate::leanh::lean_dec(v___y_4573_);
    crate::leanh::lean_dec_ref(v___y_4572_);
    crate::leanh::lean_dec(v___y_4571_);
    crate::leanh::lean_dec_ref(v___y_4570_);
    return v_res_4575_;
}
pub unsafe fn l_Lean_Meta_Sym_unfoldReducibleStep(
    mut v_e_4578_: *mut crate::leanh::LeanObject,
    mut v_a_4579_: *mut crate::leanh::LeanObject,
    mut v_a_4580_: *mut crate::leanh::LeanObject,
    mut v_a_4581_: *mut crate::leanh::LeanObject,
    mut v_a_4582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4590_: u8 = 0;
    let mut v___x_4591_: u8 = 0;
    let mut v___x_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: u8 = 0;
    let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: u8 = 0;
    let mut v___x_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4604_: u8 = 0;
    let mut v_val_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4608_: u8 = 0;
    let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4615_: u8 = 0;
    let mut v___x_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4620_: u8 = 0;
    let mut v_a_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4624_: u8 = 0;
    let mut v___x_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4628_: u8 = 0;
    let mut v___x_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4637_: u8 = 0;
    let mut v_a_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4641_: u8 = 0;
    let mut v___x_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4645_: u8 = 0;
    let mut v___x_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4584_ = l_Lean_Expr_getAppFn(v_e_4578_);
                if crate::leanh::lean_obj_tag(v___x_4584_) == 4 {
                    v_declName_4585_ = crate::leanh::lean_ctor_get(v___x_4584_, 0);
                    crate::leanh::lean_inc_n(v_declName_4585_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_4584_, 2);
                    v___x_4586_ =
                        l_Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0(
                            v_declName_4585_,
                            v_a_4579_,
                            v_a_4580_,
                            v_a_4581_,
                            v_a_4582_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_4586_) == 0 {
                        v_a_4587_ = crate::leanh::lean_ctor_get(v___x_4586_, 0);
                        v_isSharedCheck_4637_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4586_)) as u8;
                        if v_isSharedCheck_4637_ == 0 {
                            v___x_4589_ = v___x_4586_;
                            v_isShared_4590_ = v_isSharedCheck_4637_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4587_);
                            crate::leanh::lean_dec(v___x_4586_);
                            v___x_4589_ = crate::leanh::lean_box(0);
                            v_isShared_4590_ = v_isSharedCheck_4637_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_declName_4585_);
                        crate::leanh::lean_dec_ref(v_e_4578_);
                        v_a_4638_ = crate::leanh::lean_ctor_get(v___x_4586_, 0);
                        v_isSharedCheck_4645_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4586_)) as u8;
                        if v_isSharedCheck_4645_ == 0 {
                            v___x_4640_ = v___x_4586_;
                            v_isShared_4641_ = v_isSharedCheck_4645_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4638_);
                            crate::leanh::lean_dec(v___x_4586_);
                            v___x_4640_ = crate::leanh::lean_box(0);
                            v_isShared_4641_ = v_isSharedCheck_4645_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_4584_);
                    crate::leanh::lean_dec_ref(v_e_4578_);
                    v___x_4646_ = l_Lean_Meta_Sym_unfoldReducibleStep___closed__0;
                    v___x_4647_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4647_, 0, v___x_4646_);
                    return v___x_4647_;
                }
            }
            1 => {
                v___x_4591_ = (crate::leanh::lean_unbox(v_a_4587_) as u8);
                crate::leanh::lean_dec(v_a_4587_);
                if v___x_4591_ == 0 {
                    crate::leanh::lean_dec(v_declName_4585_);
                    crate::leanh::lean_dec_ref(v_e_4578_);
                    v___x_4592_ = l_Lean_Meta_Sym_unfoldReducibleStep___closed__0;
                    if v_isShared_4590_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4589_, 0, v___x_4592_);
                        v___x_4594_ = v___x_4589_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4595_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4595_, 0, v___x_4592_);
                        v___x_4594_ = v_reuseFailAlloc_4595_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4596_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget(
                        v_declName_4585_,
                    );
                    if v___x_4596_ == 0 {
                        v___x_4597_ = lean_st_ref_get(v_a_4582_);
                        v_env_4598_ = crate::leanh::lean_ctor_get(v___x_4597_, 0);
                        crate::leanh::lean_inc_ref(v_env_4598_);
                        crate::leanh::lean_dec(v___x_4597_);
                        v___x_4599_ =
                            l_Lean_Environment_isProjectionFn(v_env_4598_, v_declName_4585_);
                        if v___x_4599_ == 0 {
                            crate::leanh::lean_del_object(v___x_4589_);
                            v___x_4600_ = l_Lean_Meta_unfoldDefinition_x3f(
                                v_e_4578_,
                                v___x_4599_,
                                v_a_4579_,
                                v_a_4580_,
                                v_a_4581_,
                                v_a_4582_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4600_) == 0 {
                                v_a_4601_ = crate::leanh::lean_ctor_get(v___x_4600_, 0);
                                v_isSharedCheck_4620_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4600_)) as u8;
                                if v_isSharedCheck_4620_ == 0 {
                                    v___x_4603_ = v___x_4600_;
                                    v_isShared_4604_ = v_isSharedCheck_4620_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4601_);
                                    crate::leanh::lean_dec(v___x_4600_);
                                    v___x_4603_ = crate::leanh::lean_box(0);
                                    v_isShared_4604_ = v_isSharedCheck_4620_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                v_a_4621_ = crate::leanh::lean_ctor_get(v___x_4600_, 0);
                                v_isSharedCheck_4628_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4600_)) as u8;
                                if v_isSharedCheck_4628_ == 0 {
                                    v___x_4623_ = v___x_4600_;
                                    v_isShared_4624_ = v_isSharedCheck_4628_;
                                    state = 8;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4621_);
                                    crate::leanh::lean_dec(v___x_4600_);
                                    v___x_4623_ = crate::leanh::lean_box(0);
                                    v_isShared_4624_ = v_isSharedCheck_4628_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_e_4578_);
                            v___x_4629_ = l_Lean_Meta_Sym_unfoldReducibleStep___closed__0;
                            if v_isShared_4590_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4589_, 0, v___x_4629_);
                                v___x_4631_ = v___x_4589_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_4632_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4632_, 0, v___x_4629_);
                                v___x_4631_ = v_reuseFailAlloc_4632_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_declName_4585_);
                        crate::leanh::lean_dec_ref(v_e_4578_);
                        v___x_4633_ = l_Lean_Meta_Sym_unfoldReducibleStep___closed__0;
                        if v_isShared_4590_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4589_, 0, v___x_4633_);
                            v___x_4635_ = v___x_4589_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_4636_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4636_, 0, v___x_4633_);
                            v___x_4635_ = v_reuseFailAlloc_4636_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4594_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_4601_) == 1 {
                    v_val_4605_ = crate::leanh::lean_ctor_get(v_a_4601_, 0);
                    v_isSharedCheck_4615_ = (!crate::leanh::lean_is_exclusive(v_a_4601_)) as u8;
                    if v_isSharedCheck_4615_ == 0 {
                        v___x_4607_ = v_a_4601_;
                        v_isShared_4608_ = v_isSharedCheck_4615_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4605_);
                        crate::leanh::lean_dec(v_a_4601_);
                        v___x_4607_ = crate::leanh::lean_box(0);
                        v_isShared_4608_ = v_isSharedCheck_4615_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4601_);
                    v___x_4616_ = l_Lean_Meta_Sym_unfoldReducibleStep___closed__0;
                    if v_isShared_4604_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4603_, 0, v___x_4616_);
                        v___x_4618_ = v___x_4603_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4619_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4619_, 0, v___x_4616_);
                        v___x_4618_ = v_reuseFailAlloc_4619_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4608_ == 0 {
                    v___x_4610_ = v___x_4607_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4614_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4614_, 0, v_val_4605_);
                    v___x_4610_ = v_reuseFailAlloc_4614_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4604_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4603_, 0, v___x_4610_);
                    v___x_4612_ = v___x_4603_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4613_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4613_, 0, v___x_4610_);
                    v___x_4612_ = v_reuseFailAlloc_4613_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4612_;
            }
            7 => {
                return v___x_4618_;
            }
            8 => {
                if v_isShared_4624_ == 0 {
                    v___x_4626_ = v___x_4623_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4627_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4627_, 0, v_a_4621_);
                    v___x_4626_ = v_reuseFailAlloc_4627_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4626_;
            }
            10 => {
                return v___x_4631_;
            }
            11 => {
                return v___x_4635_;
            }
            12 => {
                if v_isShared_4641_ == 0 {
                    v___x_4643_ = v___x_4640_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4644_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4644_, 0, v_a_4638_);
                    v___x_4643_ = v_reuseFailAlloc_4644_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4643_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_unfoldReducibleStep___boxed(
    mut v_e_4648_: *mut crate::leanh::LeanObject,
    mut v_a_4649_: *mut crate::leanh::LeanObject,
    mut v_a_4650_: *mut crate::leanh::LeanObject,
    mut v_a_4651_: *mut crate::leanh::LeanObject,
    mut v_a_4652_: *mut crate::leanh::LeanObject,
    mut v_a_4653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4654_ =
        l_Lean_Meta_Sym_unfoldReducibleStep(v_e_4648_, v_a_4649_, v_a_4650_, v_a_4651_, v_a_4652_);
    crate::leanh::lean_dec(v_a_4652_);
    crate::leanh::lean_dec_ref(v_a_4651_);
    crate::leanh::lean_dec(v_a_4650_);
    crate::leanh::lean_dec_ref(v_a_4649_);
    return v_res_4654_;
}
pub unsafe fn l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0_spec__0(
    mut v_declName_4655_: *mut crate::leanh::LeanObject,
    mut v___y_4656_: *mut crate::leanh::LeanObject,
    mut v___y_4657_: *mut crate::leanh::LeanObject,
    mut v___y_4658_: *mut crate::leanh::LeanObject,
    mut v___y_4659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4661_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0_spec__0___redArg(v_declName_4655_, v___y_4659_);
    return v___x_4661_;
}
pub unsafe fn l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0_spec__0___boxed(
    mut v_declName_4662_: *mut crate::leanh::LeanObject,
    mut v___y_4663_: *mut crate::leanh::LeanObject,
    mut v___y_4664_: *mut crate::leanh::LeanObject,
    mut v___y_4665_: *mut crate::leanh::LeanObject,
    mut v___y_4666_: *mut crate::leanh::LeanObject,
    mut v___y_4667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4668_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0_spec__0(v_declName_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_);
    crate::leanh::lean_dec(v___y_4666_);
    crate::leanh::lean_dec_ref(v___y_4665_);
    crate::leanh::lean_dec(v___y_4664_);
    crate::leanh::lean_dec_ref(v___y_4663_);
    return v_res_4668_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0(
    mut v_env_4669_: *mut crate::leanh::LeanObject,
    mut v_e_4670_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_e_4670_) == 4 {
        let mut v_declName_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4672_: u8 = 0;
        v_declName_4671_ = crate::leanh::lean_ctor_get(v_e_4670_, 0);
        crate::leanh::lean_inc_n(v_declName_4671_, 2);
        crate::leanh::lean_dec_ref_known(v_e_4670_, 2);
        crate::leanh::lean_inc_ref(v_env_4669_);
        v___x_4672_ = lean_get_reducibility_status(v_env_4669_, v_declName_4671_);
        if v___x_4672_ == 0 {
            let mut v___x_4673_: u8 = 0;
            v___x_4673_ =
                l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget(v_declName_4671_);
            if v___x_4673_ == 0 {
                let mut v___x_4674_: u8 = 0;
                v___x_4674_ = l_Lean_Environment_isProjectionFn(v_env_4669_, v_declName_4671_);
                if v___x_4674_ == 0 {
                    let mut v___x_4675_: u8 = 0;
                    v___x_4675_ = 1;
                    return v___x_4675_;
                } else {
                    return v___x_4673_;
                }
            } else {
                let mut v___x_4676_: u8 = 0;
                crate::leanh::lean_dec(v_declName_4671_);
                crate::leanh::lean_dec_ref(v_env_4669_);
                v___x_4676_ = 0;
                return v___x_4676_;
            }
        } else {
            let mut v___x_4677_: u8 = 0;
            crate::leanh::lean_dec(v_declName_4671_);
            crate::leanh::lean_dec_ref(v_env_4669_);
            v___x_4677_ = 0;
            return v___x_4677_;
        }
    } else {
        let mut v___x_4678_: u8 = 0;
        crate::leanh::lean_dec_ref(v_e_4670_);
        crate::leanh::lean_dec_ref(v_env_4669_);
        v___x_4678_ = 0;
        return v___x_4678_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0___boxed(
    mut v_env_4679_: *mut crate::leanh::LeanObject,
    mut v_e_4680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4681_: u8 = 0;
    let mut v_r_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4681_ =
        l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0(
            v_env_4679_,
            v_e_4680_,
        );
    v_r_4682_ = crate::leanh::lean_box((v_res_4681_) as usize);
    return v_r_4682_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(
    mut v_e_4683_: *mut crate::leanh::LeanObject,
    mut v_a_4684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: u8 = 0;
    let mut v___x_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4695_: u8 = 0;
    let mut v___x_4696_: u8 = 0;
    let mut v___x_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4701_: u8 = 0;
    let mut v_unused_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4686_ = lean_st_ref_get(v_a_4684_);
                v_env_4687_ = crate::leanh::lean_ctor_get(v___x_4686_, 0);
                crate::leanh::lean_inc_ref(v_env_4687_);
                crate::leanh::lean_dec(v___x_4686_);
                v___f_4688_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                crate::leanh::lean_closure_set(v___f_4688_, 0, v_env_4687_);
                v___x_4689_ = lean_find_expr(v___f_4688_, v_e_4683_);
                crate::leanh::lean_dec_ref(v___f_4688_);
                if crate::leanh::lean_obj_tag(v___x_4689_) == 0 {
                    v___x_4690_ = 0;
                    v___x_4691_ = crate::leanh::lean_box((v___x_4690_) as usize);
                    v___x_4692_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4692_, 0, v___x_4691_);
                    return v___x_4692_;
                } else {
                    v_isSharedCheck_4701_ = (!crate::leanh::lean_is_exclusive(v___x_4689_)) as u8;
                    if v_isSharedCheck_4701_ == 0 {
                        v_unused_4702_ = crate::leanh::lean_ctor_get(v___x_4689_, 0);
                        crate::leanh::lean_dec(v_unused_4702_);
                        v___x_4694_ = v___x_4689_;
                        v_isShared_4695_ = v_isSharedCheck_4701_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4689_);
                        v___x_4694_ = crate::leanh::lean_box(0);
                        v_isShared_4695_ = v_isSharedCheck_4701_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4696_ = 1;
                v___x_4697_ = crate::leanh::lean_box((v___x_4696_) as usize);
                if v_isShared_4695_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4694_, 0);
                    crate::leanh::lean_ctor_set(v___x_4694_, 0, v___x_4697_);
                    v___x_4699_ = v___x_4694_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4700_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4700_, 0, v___x_4697_);
                    v___x_4699_ = v_reuseFailAlloc_4700_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4699_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___boxed(
    mut v_e_4703_: *mut crate::leanh::LeanObject,
    mut v_a_4704_: *mut crate::leanh::LeanObject,
    mut v_a_4705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4706_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(
        v_e_4703_, v_a_4704_,
    );
    crate::leanh::lean_dec(v_a_4704_);
    crate::leanh::lean_dec_ref(v_e_4703_);
    return v_res_4706_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget(
    mut v_e_4707_: *mut crate::leanh::LeanObject,
    mut v_a_4708_: *mut crate::leanh::LeanObject,
    mut v_a_4709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4711_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(
        v_e_4707_, v_a_4709_,
    );
    return v___x_4711_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget___boxed(
    mut v_e_4712_: *mut crate::leanh::LeanObject,
    mut v_a_4713_: *mut crate::leanh::LeanObject,
    mut v_a_4714_: *mut crate::leanh::LeanObject,
    mut v_a_4715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4716_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget(
        v_e_4712_, v_a_4713_, v_a_4714_,
    );
    crate::leanh::lean_dec(v_a_4714_);
    crate::leanh::lean_dec_ref(v_a_4713_);
    crate::leanh::lean_dec_ref(v_e_4712_);
    return v_res_4716_;
}
pub unsafe fn l_Lean_Meta_Sym_unfoldReducible___lam__0(
    mut v_e_4717_: *mut crate::leanh::LeanObject,
    mut v___y_4718_: *mut crate::leanh::LeanObject,
    mut v___y_4719_: *mut crate::leanh::LeanObject,
    mut v___y_4720_: *mut crate::leanh::LeanObject,
    mut v___y_4721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4723_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4723_, 0, v_e_4717_);
    v___x_4724_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4724_, 0, v___x_4723_);
    return v___x_4724_;
}
pub unsafe fn l_Lean_Meta_Sym_unfoldReducible___lam__0___boxed(
    mut v_e_4725_: *mut crate::leanh::LeanObject,
    mut v___y_4726_: *mut crate::leanh::LeanObject,
    mut v___y_4727_: *mut crate::leanh::LeanObject,
    mut v___y_4728_: *mut crate::leanh::LeanObject,
    mut v___y_4729_: *mut crate::leanh::LeanObject,
    mut v___y_4730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4731_ = l_Lean_Meta_Sym_unfoldReducible___lam__0(
        v_e_4725_,
        v___y_4726_,
        v___y_4727_,
        v___y_4728_,
        v___y_4729_,
    );
    crate::leanh::lean_dec(v___y_4729_);
    crate::leanh::lean_dec_ref(v___y_4728_);
    crate::leanh::lean_dec(v___y_4727_);
    crate::leanh::lean_dec_ref(v___y_4726_);
    return v_res_4731_;
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(
    mut v_00_u03b1_4732_: *mut crate::leanh::LeanObject,
    mut v_x_4733_: *mut crate::leanh::LeanObject,
    mut v___y_4734_: *mut crate::leanh::LeanObject,
    mut v___y_4735_: *mut crate::leanh::LeanObject,
    mut v___y_4736_: *mut crate::leanh::LeanObject,
    mut v___y_4737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4739_ = crate::leanh::lean_apply_1(v_x_4733_, crate::leanh::lean_box(0));
    v___x_4740_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4740_, 0, v___x_4739_);
    return v___x_4740_;
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0___boxed(
    mut v_00_u03b1_4741_: *mut crate::leanh::LeanObject,
    mut v_x_4742_: *mut crate::leanh::LeanObject,
    mut v___y_4743_: *mut crate::leanh::LeanObject,
    mut v___y_4744_: *mut crate::leanh::LeanObject,
    mut v___y_4745_: *mut crate::leanh::LeanObject,
    mut v___y_4746_: *mut crate::leanh::LeanObject,
    mut v___y_4747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4748_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(
        v_00_u03b1_4741_,
        v_x_4742_,
        v___y_4743_,
        v___y_4744_,
        v___y_4745_,
        v___y_4746_,
    );
    crate::leanh::lean_dec(v___y_4746_);
    crate::leanh::lean_dec_ref(v___y_4745_);
    crate::leanh::lean_dec(v___y_4744_);
    crate::leanh::lean_dec_ref(v___y_4743_);
    return v_res_4748_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(
    mut v_a_4749_: *mut crate::leanh::LeanObject,
    mut v_x_4750_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4751_: u8 = 0;
    let mut v_key_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4750_) == 0 {
                    v___x_4751_ = 0;
                    return v___x_4751_;
                } else {
                    v_key_4752_ = crate::leanh::lean_ctor_get(v_x_4750_, 0);
                    v_tail_4753_ = crate::leanh::lean_ctor_get(v_x_4750_, 2);
                    v___x_4754_ = l_Lean_ExprStructEq_beq(v_key_4752_, v_a_4749_);
                    if v___x_4754_ == 0 {
                        v_x_4750_ = v_tail_4753_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4754_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg___boxed(
    mut v_a_4756_: *mut crate::leanh::LeanObject,
    mut v_x_4757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4758_: u8 = 0;
    let mut v_r_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4758_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_4756_, v_x_4757_);
    crate::leanh::lean_dec(v_x_4757_);
    crate::leanh::lean_dec_ref(v_a_4756_);
    v_r_4759_ = crate::leanh::lean_box((v_res_4758_) as usize);
    return v_r_4759_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(
    mut v_x_4760_: *mut crate::leanh::LeanObject,
    mut v_x_4761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4767_: u8 = 0;
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: u64 = 0;
    let mut v___x_4770_: u64 = 0;
    let mut v___x_4771_: u64 = 0;
    let mut v_fold_4772_: u64 = 0;
    let mut v___x_4773_: u64 = 0;
    let mut v___x_4774_: u64 = 0;
    let mut v___x_4775_: u64 = 0;
    let mut v___x_4776_: usize = 0;
    let mut v___x_4777_: usize = 0;
    let mut v___x_4778_: usize = 0;
    let mut v___x_4779_: usize = 0;
    let mut v___x_4780_: usize = 0;
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4787_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4761_) == 0 {
                    return v_x_4760_;
                } else {
                    v_key_4762_ = crate::leanh::lean_ctor_get(v_x_4761_, 0);
                    v_value_4763_ = crate::leanh::lean_ctor_get(v_x_4761_, 1);
                    v_tail_4764_ = crate::leanh::lean_ctor_get(v_x_4761_, 2);
                    v_isSharedCheck_4787_ = (!crate::leanh::lean_is_exclusive(v_x_4761_)) as u8;
                    if v_isSharedCheck_4787_ == 0 {
                        v___x_4766_ = v_x_4761_;
                        v_isShared_4767_ = v_isSharedCheck_4787_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4764_);
                        crate::leanh::lean_inc(v_value_4763_);
                        crate::leanh::lean_inc(v_key_4762_);
                        crate::leanh::lean_dec(v_x_4761_);
                        v___x_4766_ = crate::leanh::lean_box(0);
                        v_isShared_4767_ = v_isSharedCheck_4787_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4768_ = lean_array_get_size(v_x_4760_);
                v___x_4769_ = l_Lean_ExprStructEq_hash(v_key_4762_);
                v___x_4770_ = 32u64;
                v___x_4771_ = lean_uint64_shift_right(v___x_4769_, v___x_4770_);
                v_fold_4772_ = lean_uint64_xor(v___x_4769_, v___x_4771_);
                v___x_4773_ = 16u64;
                v___x_4774_ = lean_uint64_shift_right(v_fold_4772_, v___x_4773_);
                v___x_4775_ = lean_uint64_xor(v_fold_4772_, v___x_4774_);
                v___x_4776_ = lean_uint64_to_usize(v___x_4775_);
                v___x_4777_ = lean_usize_of_nat(v___x_4768_);
                v___x_4778_ = 1usize;
                v___x_4779_ = lean_usize_sub(v___x_4777_, v___x_4778_);
                v___x_4780_ = lean_usize_land(v___x_4776_, v___x_4779_);
                v___x_4781_ = lean_array_uget_borrowed(v_x_4760_, v___x_4780_);
                crate::leanh::lean_inc(v___x_4781_);
                if v_isShared_4767_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4766_, 2, v___x_4781_);
                    v___x_4783_ = v___x_4766_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4786_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4786_, 0, v_key_4762_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4786_, 1, v_value_4763_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4786_, 2, v___x_4781_);
                    v___x_4783_ = v_reuseFailAlloc_4786_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4784_ = lean_array_uset(v_x_4760_, v___x_4780_, v___x_4783_);
                v_x_4760_ = v___x_4784_;
                v_x_4761_ = v_tail_4764_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(
    mut v_i_4788_: *mut crate::leanh::LeanObject,
    mut v_source_4789_: *mut crate::leanh::LeanObject,
    mut v_target_4790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: u8 = 0;
    let mut v_es_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4791_ = lean_array_get_size(v_source_4789_);
                v___x_4792_ = lean_nat_dec_lt(v_i_4788_, v___x_4791_);
                if v___x_4792_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_4789_);
                    crate::leanh::lean_dec(v_i_4788_);
                    return v_target_4790_;
                } else {
                    v_es_4793_ = lean_array_fget(v_source_4789_, v_i_4788_);
                    v___x_4794_ = crate::leanh::lean_box(0);
                    v_source_4795_ = lean_array_fset(v_source_4789_, v_i_4788_, v___x_4794_);
                    v_target_4796_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_target_4790_, v_es_4793_);
                    v___x_4797_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4798_ = lean_nat_add(v_i_4788_, v___x_4797_);
                    crate::leanh::lean_dec(v_i_4788_);
                    v_i_4788_ = v___x_4798_;
                    v_source_4789_ = v_source_4795_;
                    v_target_4790_ = v_target_4796_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(
    mut v_data_4800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4801_ = lean_array_get_size(v_data_4800_);
    v___x_4802_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_4803_ = lean_nat_mul(v___x_4801_, v___x_4802_);
    v___x_4804_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4805_ = crate::leanh::lean_box(0);
    v___x_4806_ = lean_mk_array(v_nbuckets_4803_, v___x_4805_);
    v___x_4807_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v___x_4804_, v_data_4800_, v___x_4806_);
    return v___x_4807_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(
    mut v_a_4808_: *mut crate::leanh::LeanObject,
    mut v_b_4809_: *mut crate::leanh::LeanObject,
    mut v_x_4810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4816_: u8 = 0;
    let mut v___x_4817_: u8 = 0;
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4825_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4810_) == 0 {
                    crate::leanh::lean_dec(v_b_4809_);
                    crate::leanh::lean_dec_ref(v_a_4808_);
                    return v_x_4810_;
                } else {
                    v_key_4811_ = crate::leanh::lean_ctor_get(v_x_4810_, 0);
                    v_value_4812_ = crate::leanh::lean_ctor_get(v_x_4810_, 1);
                    v_tail_4813_ = crate::leanh::lean_ctor_get(v_x_4810_, 2);
                    v_isSharedCheck_4825_ = (!crate::leanh::lean_is_exclusive(v_x_4810_)) as u8;
                    if v_isSharedCheck_4825_ == 0 {
                        v___x_4815_ = v_x_4810_;
                        v_isShared_4816_ = v_isSharedCheck_4825_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4813_);
                        crate::leanh::lean_inc(v_value_4812_);
                        crate::leanh::lean_inc(v_key_4811_);
                        crate::leanh::lean_dec(v_x_4810_);
                        v___x_4815_ = crate::leanh::lean_box(0);
                        v_isShared_4816_ = v_isSharedCheck_4825_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4817_ = l_Lean_ExprStructEq_beq(v_key_4811_, v_a_4808_);
                if v___x_4817_ == 0 {
                    v___x_4818_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_4808_, v_b_4809_, v_tail_4813_);
                    if v_isShared_4816_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4815_, 2, v___x_4818_);
                        v___x_4820_ = v___x_4815_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4821_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4821_, 0, v_key_4811_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4821_, 1, v_value_4812_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4821_, 2, v___x_4818_);
                        v___x_4820_ = v_reuseFailAlloc_4821_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_4812_);
                    crate::leanh::lean_dec(v_key_4811_);
                    if v_isShared_4816_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4815_, 1, v_b_4809_);
                        crate::leanh::lean_ctor_set(v___x_4815_, 0, v_a_4808_);
                        v___x_4823_ = v___x_4815_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4824_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4824_, 0, v_a_4808_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4824_, 1, v_b_4809_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4824_, 2, v_tail_4813_);
                        v___x_4823_ = v_reuseFailAlloc_4824_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4820_;
            }
            3 => {
                return v___x_4823_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(
    mut v_m_4826_: *mut crate::leanh::LeanObject,
    mut v_a_4827_: *mut crate::leanh::LeanObject,
    mut v_b_4828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4833_: u8 = 0;
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: u64 = 0;
    let mut v___x_4836_: u64 = 0;
    let mut v___x_4837_: u64 = 0;
    let mut v_fold_4838_: u64 = 0;
    let mut v___x_4839_: u64 = 0;
    let mut v___x_4840_: u64 = 0;
    let mut v___x_4841_: u64 = 0;
    let mut v___x_4842_: usize = 0;
    let mut v___x_4843_: usize = 0;
    let mut v___x_4844_: usize = 0;
    let mut v___x_4845_: usize = 0;
    let mut v___x_4846_: usize = 0;
    let mut v_bkt_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: u8 = 0;
    let mut v___x_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: u8 = 0;
    let mut v_val_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4873_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4829_ = crate::leanh::lean_ctor_get(v_m_4826_, 0);
                v_buckets_4830_ = crate::leanh::lean_ctor_get(v_m_4826_, 1);
                v_isSharedCheck_4873_ = (!crate::leanh::lean_is_exclusive(v_m_4826_)) as u8;
                if v_isSharedCheck_4873_ == 0 {
                    v___x_4832_ = v_m_4826_;
                    v_isShared_4833_ = v_isSharedCheck_4873_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_4830_);
                    crate::leanh::lean_inc(v_size_4829_);
                    crate::leanh::lean_dec(v_m_4826_);
                    v___x_4832_ = crate::leanh::lean_box(0);
                    v_isShared_4833_ = v_isSharedCheck_4873_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4834_ = lean_array_get_size(v_buckets_4830_);
                v___x_4835_ = l_Lean_ExprStructEq_hash(v_a_4827_);
                v___x_4836_ = 32u64;
                v___x_4837_ = lean_uint64_shift_right(v___x_4835_, v___x_4836_);
                v_fold_4838_ = lean_uint64_xor(v___x_4835_, v___x_4837_);
                v___x_4839_ = 16u64;
                v___x_4840_ = lean_uint64_shift_right(v_fold_4838_, v___x_4839_);
                v___x_4841_ = lean_uint64_xor(v_fold_4838_, v___x_4840_);
                v___x_4842_ = lean_uint64_to_usize(v___x_4841_);
                v___x_4843_ = lean_usize_of_nat(v___x_4834_);
                v___x_4844_ = 1usize;
                v___x_4845_ = lean_usize_sub(v___x_4843_, v___x_4844_);
                v___x_4846_ = lean_usize_land(v___x_4842_, v___x_4845_);
                v_bkt_4847_ = lean_array_uget_borrowed(v_buckets_4830_, v___x_4846_);
                v___x_4848_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_4827_, v_bkt_4847_);
                if v___x_4848_ == 0 {
                    v___x_4849_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_4850_ = lean_nat_add(v_size_4829_, v___x_4849_);
                    crate::leanh::lean_dec(v_size_4829_);
                    crate::leanh::lean_inc(v_bkt_4847_);
                    v___x_4851_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4851_, 0, v_a_4827_);
                    crate::leanh::lean_ctor_set(v___x_4851_, 1, v_b_4828_);
                    crate::leanh::lean_ctor_set(v___x_4851_, 2, v_bkt_4847_);
                    v_buckets_x27_4852_ =
                        lean_array_uset(v_buckets_4830_, v___x_4846_, v___x_4851_);
                    v___x_4853_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_4854_ = lean_nat_mul(v_size_x27_4850_, v___x_4853_);
                    v___x_4855_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_4856_ = lean_nat_div(v___x_4854_, v___x_4855_);
                    crate::leanh::lean_dec(v___x_4854_);
                    v___x_4857_ = lean_array_get_size(v_buckets_x27_4852_);
                    v___x_4858_ = lean_nat_dec_le(v___x_4856_, v___x_4857_);
                    crate::leanh::lean_dec(v___x_4856_);
                    if v___x_4858_ == 0 {
                        v_val_4859_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(v_buckets_x27_4852_);
                        if v_isShared_4833_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4832_, 1, v_val_4859_);
                            crate::leanh::lean_ctor_set(v___x_4832_, 0, v_size_x27_4850_);
                            v___x_4861_ = v___x_4832_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4862_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4862_,
                                0,
                                v_size_x27_4850_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4862_, 1, v_val_4859_);
                            v___x_4861_ = v_reuseFailAlloc_4862_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_4833_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4832_, 1, v_buckets_x27_4852_);
                            crate::leanh::lean_ctor_set(v___x_4832_, 0, v_size_x27_4850_);
                            v___x_4864_ = v___x_4832_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4865_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4865_,
                                0,
                                v_size_x27_4850_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4865_,
                                1,
                                v_buckets_x27_4852_,
                            );
                            v___x_4864_ = v_reuseFailAlloc_4865_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_4847_);
                    v___x_4866_ = crate::leanh::lean_box(0);
                    v_buckets_x27_4867_ =
                        lean_array_uset(v_buckets_4830_, v___x_4846_, v___x_4866_);
                    v___x_4868_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_4827_, v_b_4828_, v_bkt_4847_);
                    v___x_4869_ = lean_array_uset(v_buckets_x27_4867_, v___x_4846_, v___x_4868_);
                    if v_isShared_4833_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4832_, 1, v___x_4869_);
                        v___x_4871_ = v___x_4832_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4872_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4872_, 0, v_size_4829_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4872_, 1, v___x_4869_);
                        v___x_4871_ = v_reuseFailAlloc_4872_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4861_;
            }
            3 => {
                return v___x_4864_;
            }
            4 => {
                return v___x_4871_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(
    mut v_a_4874_: *mut crate::leanh::LeanObject,
    mut v_e_4875_: *mut crate::leanh::LeanObject,
    mut v_a_4876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4878_ = lean_st_ref_take(v_a_4874_);
    v___x_4879_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v___x_4878_, v_e_4875_, v_a_4876_);
    v___x_4880_ = lean_st_ref_set(v_a_4874_, v___x_4879_);
    v___x_4881_ = crate::leanh::lean_box(0);
    return v___x_4881_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed(
    mut v_a_4882_: *mut crate::leanh::LeanObject,
    mut v_e_4883_: *mut crate::leanh::LeanObject,
    mut v_a_4884_: *mut crate::leanh::LeanObject,
    mut v___y_4885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4886_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(v_a_4882_, v_e_4883_, v_a_4884_);
    crate::leanh::lean_dec(v_a_4882_);
    return v_res_4886_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4892_ = l_Lean_maxRecDepthErrorMessage;
    v___x_4893_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4893_, 0, v___x_4892_);
    return v___x_4893_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4894_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3);
    v___x_4895_ = l_Lean_MessageData_ofFormat(v___x_4894_);
    return v___x_4895_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4896_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4);
    v___x_4897_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2;
    v___x_4898_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4898_, 0, v___x_4897_);
    crate::leanh::lean_ctor_set(v___x_4898_, 1, v___x_4896_);
    return v___x_4898_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(
    mut v_ref_4899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4901_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
    v___x_4902_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4902_, 0, v_ref_4899_);
    crate::leanh::lean_ctor_set(v___x_4902_, 1, v___x_4901_);
    v___x_4903_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4903_, 0, v___x_4902_);
    return v___x_4903_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___boxed(
    mut v_ref_4904_: *mut crate::leanh::LeanObject,
    mut v___y_4905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4906_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_4904_);
    return v_res_4906_;
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(
    mut v_x_4907_: *mut crate::leanh::LeanObject,
    mut v___y_4908_: *mut crate::leanh::LeanObject,
    mut v___y_4909_: *mut crate::leanh::LeanObject,
    mut v___y_4910_: *mut crate::leanh::LeanObject,
    mut v___y_4911_: *mut crate::leanh::LeanObject,
    mut v___y_4912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4919_: u8 = 0;
    let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4923_: u8 = 0;
    let mut v_fileName_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4936_: u8 = 0;
    let mut v_cancelTk_x3f_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4938_: u8 = 0;
    let mut v_inheritedTraceOptions_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: u8 = 0;
    let mut v___x_4947_: u8 = 0;
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_4924_ = crate::leanh::lean_ctor_get(v___y_4911_, 0);
                v_fileMap_4925_ = crate::leanh::lean_ctor_get(v___y_4911_, 1);
                v_options_4926_ = crate::leanh::lean_ctor_get(v___y_4911_, 2);
                v_currRecDepth_4927_ = crate::leanh::lean_ctor_get(v___y_4911_, 3);
                v_maxRecDepth_4928_ = crate::leanh::lean_ctor_get(v___y_4911_, 4);
                v_ref_4929_ = crate::leanh::lean_ctor_get(v___y_4911_, 5);
                v_currNamespace_4930_ = crate::leanh::lean_ctor_get(v___y_4911_, 6);
                v_openDecls_4931_ = crate::leanh::lean_ctor_get(v___y_4911_, 7);
                v_initHeartbeats_4932_ = crate::leanh::lean_ctor_get(v___y_4911_, 8);
                v_maxHeartbeats_4933_ = crate::leanh::lean_ctor_get(v___y_4911_, 9);
                v_quotContext_4934_ = crate::leanh::lean_ctor_get(v___y_4911_, 10);
                v_currMacroScope_4935_ = crate::leanh::lean_ctor_get(v___y_4911_, 11);
                v_diag_4936_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_4911_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4937_ = crate::leanh::lean_ctor_get(v___y_4911_, 12);
                v_suppressElabErrors_4938_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_4911_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4939_ = crate::leanh::lean_ctor_get(v___y_4911_, 13);
                v___x_4945_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4946_ = lean_nat_dec_eq(v_maxRecDepth_4928_, v___x_4945_);
                if v___x_4946_ == 0 {
                    v___x_4947_ = lean_nat_dec_eq(v_currRecDepth_4927_, v_maxRecDepth_4928_);
                    if v___x_4947_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_x_4907_);
                        crate::leanh::lean_inc(v_ref_4929_);
                        v___x_4948_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_4929_);
                        v___y_4915_ = v___x_4948_;
                        state = 1;
                        continue;
                    }
                } else {
                    state = 4;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_4915_) == 0 {
                    return v___y_4915_;
                } else {
                    v_a_4916_ = crate::leanh::lean_ctor_get(v___y_4915_, 0);
                    v_isSharedCheck_4923_ = (!crate::leanh::lean_is_exclusive(v___y_4915_)) as u8;
                    if v_isSharedCheck_4923_ == 0 {
                        v___x_4918_ = v___y_4915_;
                        v_isShared_4919_ = v_isSharedCheck_4923_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4916_);
                        crate::leanh::lean_dec(v___y_4915_);
                        v___x_4918_ = crate::leanh::lean_box(0);
                        v_isShared_4919_ = v_isSharedCheck_4923_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4919_ == 0 {
                    v___x_4921_ = v___x_4918_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4922_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_a_4916_);
                    v___x_4921_ = v_reuseFailAlloc_4922_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4921_;
            }
            4 => {
                v___x_4941_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4942_ = lean_nat_add(v_currRecDepth_4927_, v___x_4941_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_4939_);
                crate::leanh::lean_inc(v_cancelTk_x3f_4937_);
                crate::leanh::lean_inc(v_currMacroScope_4935_);
                crate::leanh::lean_inc(v_quotContext_4934_);
                crate::leanh::lean_inc(v_maxHeartbeats_4933_);
                crate::leanh::lean_inc(v_initHeartbeats_4932_);
                crate::leanh::lean_inc(v_openDecls_4931_);
                crate::leanh::lean_inc(v_currNamespace_4930_);
                crate::leanh::lean_inc(v_ref_4929_);
                crate::leanh::lean_inc(v_maxRecDepth_4928_);
                crate::leanh::lean_inc_ref(v_options_4926_);
                crate::leanh::lean_inc_ref(v_fileMap_4925_);
                crate::leanh::lean_inc_ref(v_fileName_4924_);
                v___x_4943_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_4943_, 0, v_fileName_4924_);
                crate::leanh::lean_ctor_set(v___x_4943_, 1, v_fileMap_4925_);
                crate::leanh::lean_ctor_set(v___x_4943_, 2, v_options_4926_);
                crate::leanh::lean_ctor_set(v___x_4943_, 3, v___x_4942_);
                crate::leanh::lean_ctor_set(v___x_4943_, 4, v_maxRecDepth_4928_);
                crate::leanh::lean_ctor_set(v___x_4943_, 5, v_ref_4929_);
                crate::leanh::lean_ctor_set(v___x_4943_, 6, v_currNamespace_4930_);
                crate::leanh::lean_ctor_set(v___x_4943_, 7, v_openDecls_4931_);
                crate::leanh::lean_ctor_set(v___x_4943_, 8, v_initHeartbeats_4932_);
                crate::leanh::lean_ctor_set(v___x_4943_, 9, v_maxHeartbeats_4933_);
                crate::leanh::lean_ctor_set(v___x_4943_, 10, v_quotContext_4934_);
                crate::leanh::lean_ctor_set(v___x_4943_, 11, v_currMacroScope_4935_);
                crate::leanh::lean_ctor_set(v___x_4943_, 12, v_cancelTk_x3f_4937_);
                crate::leanh::lean_ctor_set(v___x_4943_, 13, v_inheritedTraceOptions_4939_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4943_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_4936_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4943_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4938_,
                );
                crate::leanh::lean_inc(v___y_4912_);
                crate::leanh::lean_inc(v___y_4910_);
                crate::leanh::lean_inc_ref(v___y_4909_);
                crate::leanh::lean_inc(v___y_4908_);
                v___x_4944_ = crate::leanh::lean_apply_6(
                    v_x_4907_,
                    v___y_4908_,
                    v___y_4909_,
                    v___y_4910_,
                    v___x_4943_,
                    v___y_4912_,
                    crate::leanh::lean_box(0),
                );
                v___y_4915_ = v___x_4944_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg___boxed(
    mut v_x_4949_: *mut crate::leanh::LeanObject,
    mut v___y_4950_: *mut crate::leanh::LeanObject,
    mut v___y_4951_: *mut crate::leanh::LeanObject,
    mut v___y_4952_: *mut crate::leanh::LeanObject,
    mut v___y_4953_: *mut crate::leanh::LeanObject,
    mut v___y_4954_: *mut crate::leanh::LeanObject,
    mut v___y_4955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4956_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v_x_4949_, v___y_4950_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_);
    crate::leanh::lean_dec(v___y_4954_);
    crate::leanh::lean_dec_ref(v___y_4953_);
    crate::leanh::lean_dec(v___y_4952_);
    crate::leanh::lean_dec_ref(v___y_4951_);
    crate::leanh::lean_dec(v___y_4950_);
    return v_res_4956_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(
    mut v_00_u03b1_4957_: *mut crate::leanh::LeanObject,
    mut v_x_4958_: *mut crate::leanh::LeanObject,
    mut v___y_4959_: *mut crate::leanh::LeanObject,
    mut v___y_4960_: *mut crate::leanh::LeanObject,
    mut v___y_4961_: *mut crate::leanh::LeanObject,
    mut v___y_4962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4964_ = crate::leanh::lean_apply_1(v_x_4958_, crate::leanh::lean_box(0));
    v___x_4965_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4965_, 0, v___x_4964_);
    return v___x_4965_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0___boxed(
    mut v_00_u03b1_4966_: *mut crate::leanh::LeanObject,
    mut v_x_4967_: *mut crate::leanh::LeanObject,
    mut v___y_4968_: *mut crate::leanh::LeanObject,
    mut v___y_4969_: *mut crate::leanh::LeanObject,
    mut v___y_4970_: *mut crate::leanh::LeanObject,
    mut v___y_4971_: *mut crate::leanh::LeanObject,
    mut v___y_4972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4973_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(v_00_u03b1_4966_, v_x_4967_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_);
    crate::leanh::lean_dec(v___y_4971_);
    crate::leanh::lean_dec_ref(v___y_4970_);
    crate::leanh::lean_dec(v___y_4969_);
    crate::leanh::lean_dec_ref(v___y_4968_);
    return v_res_4973_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(
    mut v_a_4974_: *mut crate::leanh::LeanObject,
    mut v_x_4975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4980_: u8 = 0;
    let mut v___x_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4975_) == 0 {
                    v___x_4976_ = crate::leanh::lean_box(0);
                    return v___x_4976_;
                } else {
                    v_key_4977_ = crate::leanh::lean_ctor_get(v_x_4975_, 0);
                    v_value_4978_ = crate::leanh::lean_ctor_get(v_x_4975_, 1);
                    v_tail_4979_ = crate::leanh::lean_ctor_get(v_x_4975_, 2);
                    v___x_4980_ = l_Lean_ExprStructEq_beq(v_key_4977_, v_a_4974_);
                    if v___x_4980_ == 0 {
                        v_x_4975_ = v_tail_4979_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_4978_);
                        v___x_4982_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4982_, 0, v_value_4978_);
                        return v___x_4982_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg___boxed(
    mut v_a_4983_: *mut crate::leanh::LeanObject,
    mut v_x_4984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4985_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_4983_, v_x_4984_);
    crate::leanh::lean_dec(v_x_4984_);
    crate::leanh::lean_dec_ref(v_a_4983_);
    return v_res_4985_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(
    mut v_m_4986_: *mut crate::leanh::LeanObject,
    mut v_a_4987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: u64 = 0;
    let mut v___x_4991_: u64 = 0;
    let mut v___x_4992_: u64 = 0;
    let mut v_fold_4993_: u64 = 0;
    let mut v___x_4994_: u64 = 0;
    let mut v___x_4995_: u64 = 0;
    let mut v___x_4996_: u64 = 0;
    let mut v___x_4997_: usize = 0;
    let mut v___x_4998_: usize = 0;
    let mut v___x_4999_: usize = 0;
    let mut v___x_5000_: usize = 0;
    let mut v___x_5001_: usize = 0;
    let mut v___x_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_4988_ = crate::leanh::lean_ctor_get(v_m_4986_, 1);
    v___x_4989_ = lean_array_get_size(v_buckets_4988_);
    v___x_4990_ = l_Lean_ExprStructEq_hash(v_a_4987_);
    v___x_4991_ = 32u64;
    v___x_4992_ = lean_uint64_shift_right(v___x_4990_, v___x_4991_);
    v_fold_4993_ = lean_uint64_xor(v___x_4990_, v___x_4992_);
    v___x_4994_ = 16u64;
    v___x_4995_ = lean_uint64_shift_right(v_fold_4993_, v___x_4994_);
    v___x_4996_ = lean_uint64_xor(v_fold_4993_, v___x_4995_);
    v___x_4997_ = lean_uint64_to_usize(v___x_4996_);
    v___x_4998_ = lean_usize_of_nat(v___x_4989_);
    v___x_4999_ = 1usize;
    v___x_5000_ = lean_usize_sub(v___x_4998_, v___x_4999_);
    v___x_5001_ = lean_usize_land(v___x_4997_, v___x_5000_);
    v___x_5002_ = lean_array_uget_borrowed(v_buckets_4988_, v___x_5001_);
    v___x_5003_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_4987_, v___x_5002_);
    return v___x_5003_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___boxed(
    mut v_m_5004_: *mut crate::leanh::LeanObject,
    mut v_a_5005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5006_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_m_5004_, v_a_5005_);
    crate::leanh::lean_dec_ref(v_a_5005_);
    crate::leanh::lean_dec_ref(v_m_5004_);
    return v_res_5006_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2(
    mut v___x_5007_: *mut crate::leanh::LeanObject,
    mut v___y_5008_: *mut crate::leanh::LeanObject,
    mut v___y_5009_: *mut crate::leanh::LeanObject,
    mut v___y_5010_: *mut crate::leanh::LeanObject,
    mut v___y_5011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5013_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5013_, 0, v___x_5007_);
    return v___x_5013_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2___boxed(
    mut v___x_5014_: *mut crate::leanh::LeanObject,
    mut v___y_5015_: *mut crate::leanh::LeanObject,
    mut v___y_5016_: *mut crate::leanh::LeanObject,
    mut v___y_5017_: *mut crate::leanh::LeanObject,
    mut v___y_5018_: *mut crate::leanh::LeanObject,
    mut v___y_5019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5020_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2(v___x_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_);
    crate::leanh::lean_dec(v___y_5018_);
    crate::leanh::lean_dec_ref(v___y_5017_);
    crate::leanh::lean_dec(v___y_5016_);
    crate::leanh::lean_dec_ref(v___y_5015_);
    return v_res_5020_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(
    mut v_k_5021_: *mut crate::leanh::LeanObject,
    mut v___y_5022_: *mut crate::leanh::LeanObject,
    mut v_b_5023_: *mut crate::leanh::LeanObject,
    mut v___y_5024_: *mut crate::leanh::LeanObject,
    mut v___y_5025_: *mut crate::leanh::LeanObject,
    mut v___y_5026_: *mut crate::leanh::LeanObject,
    mut v___y_5027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_5027_);
    crate::leanh::lean_inc_ref(v___y_5026_);
    crate::leanh::lean_inc(v___y_5025_);
    crate::leanh::lean_inc_ref(v___y_5024_);
    crate::leanh::lean_inc(v___y_5022_);
    v___x_5029_ = crate::leanh::lean_apply_7(
        v_k_5021_,
        v_b_5023_,
        v___y_5022_,
        v___y_5024_,
        v___y_5025_,
        v___y_5026_,
        v___y_5027_,
        crate::leanh::lean_box(0),
    );
    return v___x_5029_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(
    mut v_k_5030_: *mut crate::leanh::LeanObject,
    mut v___y_5031_: *mut crate::leanh::LeanObject,
    mut v_b_5032_: *mut crate::leanh::LeanObject,
    mut v___y_5033_: *mut crate::leanh::LeanObject,
    mut v___y_5034_: *mut crate::leanh::LeanObject,
    mut v___y_5035_: *mut crate::leanh::LeanObject,
    mut v___y_5036_: *mut crate::leanh::LeanObject,
    mut v___y_5037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5038_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_5030_, v___y_5031_, v_b_5032_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_);
    crate::leanh::lean_dec(v___y_5036_);
    crate::leanh::lean_dec_ref(v___y_5035_);
    crate::leanh::lean_dec(v___y_5034_);
    crate::leanh::lean_dec_ref(v___y_5033_);
    crate::leanh::lean_dec(v___y_5031_);
    return v_res_5038_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(
    mut v_name_5039_: *mut crate::leanh::LeanObject,
    mut v_bi_5040_: u8,
    mut v_type_5041_: *mut crate::leanh::LeanObject,
    mut v_k_5042_: *mut crate::leanh::LeanObject,
    mut v_kind_5043_: u8,
    mut v___y_5044_: *mut crate::leanh::LeanObject,
    mut v___y_5045_: *mut crate::leanh::LeanObject,
    mut v___y_5046_: *mut crate::leanh::LeanObject,
    mut v___y_5047_: *mut crate::leanh::LeanObject,
    mut v___y_5048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5055_: u8 = 0;
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5059_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_5044_);
                v___f_5050_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
                crate::leanh::lean_closure_set(v___f_5050_, 0, v_k_5042_);
                crate::leanh::lean_closure_set(v___f_5050_, 1, v___y_5044_);
                v___x_5051_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_5039_,
                    v_bi_5040_,
                    v_type_5041_,
                    v___f_5050_,
                    v_kind_5043_,
                    v___y_5045_,
                    v___y_5046_,
                    v___y_5047_,
                    v___y_5048_,
                );
                if crate::leanh::lean_obj_tag(v___x_5051_) == 0 {
                    return v___x_5051_;
                } else {
                    v_a_5052_ = crate::leanh::lean_ctor_get(v___x_5051_, 0);
                    v_isSharedCheck_5059_ = (!crate::leanh::lean_is_exclusive(v___x_5051_)) as u8;
                    if v_isSharedCheck_5059_ == 0 {
                        v___x_5054_ = v___x_5051_;
                        v_isShared_5055_ = v_isSharedCheck_5059_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5052_);
                        crate::leanh::lean_dec(v___x_5051_);
                        v___x_5054_ = crate::leanh::lean_box(0);
                        v_isShared_5055_ = v_isSharedCheck_5059_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5055_ == 0 {
                    v___x_5057_ = v___x_5054_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5058_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5058_, 0, v_a_5052_);
                    v___x_5057_ = v_reuseFailAlloc_5058_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5057_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___boxed(
    mut v_name_5060_: *mut crate::leanh::LeanObject,
    mut v_bi_5061_: *mut crate::leanh::LeanObject,
    mut v_type_5062_: *mut crate::leanh::LeanObject,
    mut v_k_5063_: *mut crate::leanh::LeanObject,
    mut v_kind_5064_: *mut crate::leanh::LeanObject,
    mut v___y_5065_: *mut crate::leanh::LeanObject,
    mut v___y_5066_: *mut crate::leanh::LeanObject,
    mut v___y_5067_: *mut crate::leanh::LeanObject,
    mut v___y_5068_: *mut crate::leanh::LeanObject,
    mut v___y_5069_: *mut crate::leanh::LeanObject,
    mut v___y_5070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_5071_: u8 = 0;
    let mut v_kind_boxed_5072_: u8 = 0;
    let mut v_res_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_5071_ = (crate::leanh::lean_unbox(v_bi_5061_) as u8);
    v_kind_boxed_5072_ = (crate::leanh::lean_unbox(v_kind_5064_) as u8);
    v_res_5073_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_name_5060_, v_bi_boxed_5071_, v_type_5062_, v_k_5063_, v_kind_boxed_5072_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_);
    crate::leanh::lean_dec(v___y_5069_);
    crate::leanh::lean_dec_ref(v___y_5068_);
    crate::leanh::lean_dec(v___y_5067_);
    crate::leanh::lean_dec_ref(v___y_5066_);
    crate::leanh::lean_dec(v___y_5065_);
    return v_res_5073_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(
    mut v_name_5074_: *mut crate::leanh::LeanObject,
    mut v_type_5075_: *mut crate::leanh::LeanObject,
    mut v_val_5076_: *mut crate::leanh::LeanObject,
    mut v_k_5077_: *mut crate::leanh::LeanObject,
    mut v_nondep_5078_: u8,
    mut v_kind_5079_: u8,
    mut v___y_5080_: *mut crate::leanh::LeanObject,
    mut v___y_5081_: *mut crate::leanh::LeanObject,
    mut v___y_5082_: *mut crate::leanh::LeanObject,
    mut v___y_5083_: *mut crate::leanh::LeanObject,
    mut v___y_5084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5091_: u8 = 0;
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5095_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_5080_);
                v___f_5086_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
                crate::leanh::lean_closure_set(v___f_5086_, 0, v_k_5077_);
                crate::leanh::lean_closure_set(v___f_5086_, 1, v___y_5080_);
                v___x_5087_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_5074_,
                    v_type_5075_,
                    v_val_5076_,
                    v___f_5086_,
                    v_nondep_5078_,
                    v_kind_5079_,
                    v___y_5081_,
                    v___y_5082_,
                    v___y_5083_,
                    v___y_5084_,
                );
                if crate::leanh::lean_obj_tag(v___x_5087_) == 0 {
                    return v___x_5087_;
                } else {
                    v_a_5088_ = crate::leanh::lean_ctor_get(v___x_5087_, 0);
                    v_isSharedCheck_5095_ = (!crate::leanh::lean_is_exclusive(v___x_5087_)) as u8;
                    if v_isSharedCheck_5095_ == 0 {
                        v___x_5090_ = v___x_5087_;
                        v_isShared_5091_ = v_isSharedCheck_5095_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5088_);
                        crate::leanh::lean_dec(v___x_5087_);
                        v___x_5090_ = crate::leanh::lean_box(0);
                        v_isShared_5091_ = v_isSharedCheck_5095_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5091_ == 0 {
                    v___x_5093_ = v___x_5090_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5094_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5094_, 0, v_a_5088_);
                    v___x_5093_ = v_reuseFailAlloc_5094_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5093_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg___boxed(
    mut v_name_5096_: *mut crate::leanh::LeanObject,
    mut v_type_5097_: *mut crate::leanh::LeanObject,
    mut v_val_5098_: *mut crate::leanh::LeanObject,
    mut v_k_5099_: *mut crate::leanh::LeanObject,
    mut v_nondep_5100_: *mut crate::leanh::LeanObject,
    mut v_kind_5101_: *mut crate::leanh::LeanObject,
    mut v___y_5102_: *mut crate::leanh::LeanObject,
    mut v___y_5103_: *mut crate::leanh::LeanObject,
    mut v___y_5104_: *mut crate::leanh::LeanObject,
    mut v___y_5105_: *mut crate::leanh::LeanObject,
    mut v___y_5106_: *mut crate::leanh::LeanObject,
    mut v___y_5107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nondep_boxed_5108_: u8 = 0;
    let mut v_kind_boxed_5109_: u8 = 0;
    let mut v_res_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_5108_ = (crate::leanh::lean_unbox(v_nondep_5100_) as u8);
    v_kind_boxed_5109_ = (crate::leanh::lean_unbox(v_kind_5101_) as u8);
    v_res_5110_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_name_5096_, v_type_5097_, v_val_5098_, v_k_5099_, v_nondep_boxed_5108_, v_kind_boxed_5109_, v___y_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_);
    crate::leanh::lean_dec(v___y_5106_);
    crate::leanh::lean_dec_ref(v___y_5105_);
    crate::leanh::lean_dec(v___y_5104_);
    crate::leanh::lean_dec_ref(v___y_5103_);
    crate::leanh::lean_dec(v___y_5102_);
    return v_res_5110_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(
    mut v_fvars_5114_: *mut crate::leanh::LeanObject,
    mut v_pre_5115_: *mut crate::leanh::LeanObject,
    mut v_post_5116_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5117_: u8,
    mut v_skipConstInApp_5118_: u8,
    mut v_skipInstances_5119_: u8,
    mut v_body_5120_: *mut crate::leanh::LeanObject,
    mut v_x_5121_: *mut crate::leanh::LeanObject,
    mut v___y_5122_: *mut crate::leanh::LeanObject,
    mut v___y_5123_: *mut crate::leanh::LeanObject,
    mut v___y_5124_: *mut crate::leanh::LeanObject,
    mut v___y_5125_: *mut crate::leanh::LeanObject,
    mut v___y_5126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5128_ = lean_array_push(v_fvars_5114_, v_x_5121_);
    v___x_5129_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_5115_, v_post_5116_, v_usedLetOnly_5117_, v_skipConstInApp_5118_, v_skipInstances_5119_, v___x_5128_, v_body_5120_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_);
    return v___x_5129_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed(
    mut v_fvars_5130_: *mut crate::leanh::LeanObject,
    mut v_pre_5131_: *mut crate::leanh::LeanObject,
    mut v_post_5132_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5133_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_5134_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_5135_: *mut crate::leanh::LeanObject,
    mut v_body_5136_: *mut crate::leanh::LeanObject,
    mut v_x_5137_: *mut crate::leanh::LeanObject,
    mut v___y_5138_: *mut crate::leanh::LeanObject,
    mut v___y_5139_: *mut crate::leanh::LeanObject,
    mut v___y_5140_: *mut crate::leanh::LeanObject,
    mut v___y_5141_: *mut crate::leanh::LeanObject,
    mut v___y_5142_: *mut crate::leanh::LeanObject,
    mut v___y_5143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_5144_: u8 = 0;
    let mut v_skipConstInApp_boxed_5145_: u8 = 0;
    let mut v_skipInstances_boxed_5146_: u8 = 0;
    let mut v_res_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_5144_ = (crate::leanh::lean_unbox(v_usedLetOnly_5133_) as u8);
    v_skipConstInApp_boxed_5145_ = (crate::leanh::lean_unbox(v_skipConstInApp_5134_) as u8);
    v_skipInstances_boxed_5146_ = (crate::leanh::lean_unbox(v_skipInstances_5135_) as u8);
    v_res_5147_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(v_fvars_5130_, v_pre_5131_, v_post_5132_, v_usedLetOnly_boxed_5144_, v_skipConstInApp_boxed_5145_, v_skipInstances_boxed_5146_, v_body_5136_, v_x_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_);
    crate::leanh::lean_dec(v___y_5142_);
    crate::leanh::lean_dec_ref(v___y_5141_);
    crate::leanh::lean_dec(v___y_5140_);
    crate::leanh::lean_dec_ref(v___y_5139_);
    crate::leanh::lean_dec(v___y_5138_);
    return v_res_5147_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(
    mut v_pre_5148_: *mut crate::leanh::LeanObject,
    mut v_post_5149_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5150_: u8,
    mut v_skipConstInApp_5151_: u8,
    mut v_skipInstances_5152_: u8,
    mut v_e_5153_: *mut crate::leanh::LeanObject,
    mut v_a_5154_: *mut crate::leanh::LeanObject,
    mut v___y_5155_: *mut crate::leanh::LeanObject,
    mut v___y_5156_: *mut crate::leanh::LeanObject,
    mut v___y_5157_: *mut crate::leanh::LeanObject,
    mut v___y_5158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5164_: u8 = 0;
    let mut v_e_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5179_: u8 = 0;
    let mut v_a_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5183_: u8 = 0;
    let mut v___x_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5187_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_post_5149_);
                crate::leanh::lean_inc(v___y_5158_);
                crate::leanh::lean_inc_ref(v___y_5157_);
                crate::leanh::lean_inc(v___y_5156_);
                crate::leanh::lean_inc_ref(v___y_5155_);
                crate::leanh::lean_inc_ref(v_e_5153_);
                v___x_5160_ = crate::leanh::lean_apply_6(
                    v_post_5149_,
                    v_e_5153_,
                    v___y_5155_,
                    v___y_5156_,
                    v___y_5157_,
                    v___y_5158_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5160_) == 0 {
                    v_a_5161_ = crate::leanh::lean_ctor_get(v___x_5160_, 0);
                    v_isSharedCheck_5179_ = (!crate::leanh::lean_is_exclusive(v___x_5160_)) as u8;
                    if v_isSharedCheck_5179_ == 0 {
                        v___x_5163_ = v___x_5160_;
                        v_isShared_5164_ = v_isSharedCheck_5179_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5161_);
                        crate::leanh::lean_dec(v___x_5160_);
                        v___x_5163_ = crate::leanh::lean_box(0);
                        v_isShared_5164_ = v_isSharedCheck_5179_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_5153_);
                    crate::leanh::lean_dec_ref(v_post_5149_);
                    crate::leanh::lean_dec_ref(v_pre_5148_);
                    v_a_5180_ = crate::leanh::lean_ctor_get(v___x_5160_, 0);
                    v_isSharedCheck_5187_ = (!crate::leanh::lean_is_exclusive(v___x_5160_)) as u8;
                    if v_isSharedCheck_5187_ == 0 {
                        v___x_5182_ = v___x_5160_;
                        v_isShared_5183_ = v_isSharedCheck_5187_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5180_);
                        crate::leanh::lean_dec(v___x_5160_);
                        v___x_5182_ = crate::leanh::lean_box(0);
                        v_isShared_5183_ = v_isSharedCheck_5187_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => match crate::leanh::lean_obj_tag(v_a_5161_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_e_5153_);
                    crate::leanh::lean_dec_ref(v_post_5149_);
                    crate::leanh::lean_dec_ref(v_pre_5148_);
                    v_e_5165_ = crate::leanh::lean_ctor_get(v_a_5161_, 0);
                    crate::leanh::lean_inc_ref(v_e_5165_);
                    crate::leanh::lean_dec_ref_known(v_a_5161_, 1);
                    if v_isShared_5164_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5163_, 0, v_e_5165_);
                        v___x_5167_ = v___x_5163_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5168_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5168_, 0, v_e_5165_);
                        v___x_5167_ = v_reuseFailAlloc_5168_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_5163_);
                    crate::leanh::lean_dec_ref(v_e_5153_);
                    v_e_5169_ = crate::leanh::lean_ctor_get(v_a_5161_, 0);
                    crate::leanh::lean_inc_ref(v_e_5169_);
                    crate::leanh::lean_dec_ref_known(v_a_5161_, 1);
                    v___x_5170_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_5148_, v_post_5149_, v_usedLetOnly_5150_, v_skipConstInApp_5151_, v_skipInstances_5152_, v_e_5169_, v_a_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_);
                    return v___x_5170_;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_post_5149_);
                    crate::leanh::lean_dec_ref(v_pre_5148_);
                    v_e_x3f_5171_ = crate::leanh::lean_ctor_get(v_a_5161_, 0);
                    crate::leanh::lean_inc(v_e_x3f_5171_);
                    crate::leanh::lean_dec_ref_known(v_a_5161_, 1);
                    if crate::leanh::lean_obj_tag(v_e_x3f_5171_) == 0 {
                        if v_isShared_5164_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5163_, 0, v_e_5153_);
                            v___x_5173_ = v___x_5163_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5174_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5174_, 0, v_e_5153_);
                            v___x_5173_ = v_reuseFailAlloc_5174_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_5153_);
                        v_val_5175_ = crate::leanh::lean_ctor_get(v_e_x3f_5171_, 0);
                        crate::leanh::lean_inc(v_val_5175_);
                        crate::leanh::lean_dec_ref_known(v_e_x3f_5171_, 1);
                        if v_isShared_5164_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5163_, 0, v_val_5175_);
                            v___x_5177_ = v___x_5163_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5178_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5178_, 0, v_val_5175_);
                            v___x_5177_ = v_reuseFailAlloc_5178_;
                            state = 4;
                            continue;
                        }
                    }
                }
            },
            2 => {
                return v___x_5167_;
            }
            3 => {
                return v___x_5173_;
            }
            4 => {
                return v___x_5177_;
            }
            5 => {
                if v_isShared_5183_ == 0 {
                    v___x_5185_ = v___x_5182_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5186_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5186_, 0, v_a_5180_);
                    v___x_5185_ = v_reuseFailAlloc_5186_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5185_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(
    mut v_pre_5188_: *mut crate::leanh::LeanObject,
    mut v_post_5189_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5190_: u8,
    mut v_skipConstInApp_5191_: u8,
    mut v_skipInstances_5192_: u8,
    mut v_fvars_5193_: *mut crate::leanh::LeanObject,
    mut v_e_5194_: *mut crate::leanh::LeanObject,
    mut v_a_5195_: *mut crate::leanh::LeanObject,
    mut v___y_5196_: *mut crate::leanh::LeanObject,
    mut v___y_5197_: *mut crate::leanh::LeanObject,
    mut v___y_5198_: *mut crate::leanh::LeanObject,
    mut v___y_5199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_5194_) == 6 {
        let mut v_binderName_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_5204_: u8 = 0;
        let mut v___x_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_binderName_5201_ = crate::leanh::lean_ctor_get(v_e_5194_, 0);
        crate::leanh::lean_inc(v_binderName_5201_);
        v_binderType_5202_ = crate::leanh::lean_ctor_get(v_e_5194_, 1);
        crate::leanh::lean_inc_ref(v_binderType_5202_);
        v_body_5203_ = crate::leanh::lean_ctor_get(v_e_5194_, 2);
        crate::leanh::lean_inc_ref(v_body_5203_);
        v_binderInfo_5204_ = crate::leanh::lean_ctor_get_uint8(
            v_e_5194_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        );
        crate::leanh::lean_dec_ref_known(v_e_5194_, 3);
        v___x_5205_ = lean_expr_instantiate_rev(v_binderType_5202_, v_fvars_5193_);
        crate::leanh::lean_dec_ref(v_binderType_5202_);
        crate::leanh::lean_inc_ref(v_post_5189_);
        crate::leanh::lean_inc_ref(v_pre_5188_);
        v___x_5206_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_5188_, v_post_5189_, v_usedLetOnly_5190_, v_skipConstInApp_5191_, v_skipInstances_5192_, v___x_5205_, v_a_5195_, v___y_5196_, v___y_5197_, v___y_5198_, v___y_5199_);
        if crate::leanh::lean_obj_tag(v___x_5206_) == 0 {
            let mut v_a_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5212_: u8 = 0;
            let mut v___x_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_5207_ = crate::leanh::lean_ctor_get(v___x_5206_, 0);
            crate::leanh::lean_inc(v_a_5207_);
            crate::leanh::lean_dec_ref_known(v___x_5206_, 1);
            v___x_5208_ = crate::leanh::lean_box((v_usedLetOnly_5190_) as usize);
            v___x_5209_ = crate::leanh::lean_box((v_skipConstInApp_5191_) as usize);
            v___x_5210_ = crate::leanh::lean_box((v_skipInstances_5192_) as usize);
            v___f_5211_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed as *mut core::ffi::c_void, 14, 7);
            crate::leanh::lean_closure_set(v___f_5211_, 0, v_fvars_5193_);
            crate::leanh::lean_closure_set(v___f_5211_, 1, v_pre_5188_);
            crate::leanh::lean_closure_set(v___f_5211_, 2, v_post_5189_);
            crate::leanh::lean_closure_set(v___f_5211_, 3, v___x_5208_);
            crate::leanh::lean_closure_set(v___f_5211_, 4, v___x_5209_);
            crate::leanh::lean_closure_set(v___f_5211_, 5, v___x_5210_);
            crate::leanh::lean_closure_set(v___f_5211_, 6, v_body_5203_);
            v___x_5212_ = 0;
            v___x_5213_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_5201_, v_binderInfo_5204_, v_a_5207_, v___f_5211_, v___x_5212_, v_a_5195_, v___y_5196_, v___y_5197_, v___y_5198_, v___y_5199_);
            return v___x_5213_;
        } else {
            crate::leanh::lean_dec_ref(v_body_5203_);
            crate::leanh::lean_dec(v_binderName_5201_);
            crate::leanh::lean_dec_ref(v_fvars_5193_);
            crate::leanh::lean_dec_ref(v_post_5189_);
            crate::leanh::lean_dec_ref(v_pre_5188_);
            return v___x_5206_;
        }
    } else {
        let mut v___x_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5214_ = lean_expr_instantiate_rev(v_e_5194_, v_fvars_5193_);
        crate::leanh::lean_dec_ref(v_e_5194_);
        crate::leanh::lean_inc_ref(v_post_5189_);
        crate::leanh::lean_inc_ref(v_pre_5188_);
        v___x_5215_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_5188_, v_post_5189_, v_usedLetOnly_5190_, v_skipConstInApp_5191_, v_skipInstances_5192_, v___x_5214_, v_a_5195_, v___y_5196_, v___y_5197_, v___y_5198_, v___y_5199_);
        if crate::leanh::lean_obj_tag(v___x_5215_) == 0 {
            let mut v_a_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5217_: u8 = 0;
            let mut v___x_5218_: u8 = 0;
            let mut v___x_5219_: u8 = 0;
            let mut v___x_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_5216_ = crate::leanh::lean_ctor_get(v___x_5215_, 0);
            crate::leanh::lean_inc(v_a_5216_);
            crate::leanh::lean_dec_ref_known(v___x_5215_, 1);
            v___x_5217_ = 0;
            v___x_5218_ = 1;
            v___x_5219_ = 1;
            v___x_5220_ = l_Lean_Meta_mkLambdaFVars(
                v_fvars_5193_,
                v_a_5216_,
                v___x_5217_,
                v_usedLetOnly_5190_,
                v___x_5217_,
                v___x_5218_,
                v___x_5219_,
                v___y_5196_,
                v___y_5197_,
                v___y_5198_,
                v___y_5199_,
            );
            crate::leanh::lean_dec_ref(v_fvars_5193_);
            if crate::leanh::lean_obj_tag(v___x_5220_) == 0 {
                let mut v_a_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_5221_ = crate::leanh::lean_ctor_get(v___x_5220_, 0);
                crate::leanh::lean_inc(v_a_5221_);
                crate::leanh::lean_dec_ref_known(v___x_5220_, 1);
                v___x_5222_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_5188_, v_post_5189_, v_usedLetOnly_5190_, v_skipConstInApp_5191_, v_skipInstances_5192_, v_a_5221_, v_a_5195_, v___y_5196_, v___y_5197_, v___y_5198_, v___y_5199_);
                return v___x_5222_;
            } else {
                crate::leanh::lean_dec_ref(v_post_5189_);
                crate::leanh::lean_dec_ref(v_pre_5188_);
                return v___x_5220_;
            }
        } else {
            crate::leanh::lean_dec_ref(v_fvars_5193_);
            crate::leanh::lean_dec_ref(v_post_5189_);
            crate::leanh::lean_dec_ref(v_pre_5188_);
            return v___x_5215_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(
    mut v_fvars_5223_: *mut crate::leanh::LeanObject,
    mut v_pre_5224_: *mut crate::leanh::LeanObject,
    mut v_post_5225_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5226_: u8,
    mut v_skipConstInApp_5227_: u8,
    mut v_skipInstances_5228_: u8,
    mut v_body_5229_: *mut crate::leanh::LeanObject,
    mut v_x_5230_: *mut crate::leanh::LeanObject,
    mut v___y_5231_: *mut crate::leanh::LeanObject,
    mut v___y_5232_: *mut crate::leanh::LeanObject,
    mut v___y_5233_: *mut crate::leanh::LeanObject,
    mut v___y_5234_: *mut crate::leanh::LeanObject,
    mut v___y_5235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5237_ = lean_array_push(v_fvars_5223_, v_x_5230_);
    v___x_5238_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_5224_, v_post_5225_, v_usedLetOnly_5226_, v_skipConstInApp_5227_, v_skipInstances_5228_, v___x_5237_, v_body_5229_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_);
    return v___x_5238_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed(
    mut v_fvars_5239_: *mut crate::leanh::LeanObject,
    mut v_pre_5240_: *mut crate::leanh::LeanObject,
    mut v_post_5241_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5242_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_5243_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_5244_: *mut crate::leanh::LeanObject,
    mut v_body_5245_: *mut crate::leanh::LeanObject,
    mut v_x_5246_: *mut crate::leanh::LeanObject,
    mut v___y_5247_: *mut crate::leanh::LeanObject,
    mut v___y_5248_: *mut crate::leanh::LeanObject,
    mut v___y_5249_: *mut crate::leanh::LeanObject,
    mut v___y_5250_: *mut crate::leanh::LeanObject,
    mut v___y_5251_: *mut crate::leanh::LeanObject,
    mut v___y_5252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_5253_: u8 = 0;
    let mut v_skipConstInApp_boxed_5254_: u8 = 0;
    let mut v_skipInstances_boxed_5255_: u8 = 0;
    let mut v_res_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_5253_ = (crate::leanh::lean_unbox(v_usedLetOnly_5242_) as u8);
    v_skipConstInApp_boxed_5254_ = (crate::leanh::lean_unbox(v_skipConstInApp_5243_) as u8);
    v_skipInstances_boxed_5255_ = (crate::leanh::lean_unbox(v_skipInstances_5244_) as u8);
    v_res_5256_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(v_fvars_5239_, v_pre_5240_, v_post_5241_, v_usedLetOnly_boxed_5253_, v_skipConstInApp_boxed_5254_, v_skipInstances_boxed_5255_, v_body_5245_, v_x_5246_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_, v___y_5251_);
    crate::leanh::lean_dec(v___y_5251_);
    crate::leanh::lean_dec_ref(v___y_5250_);
    crate::leanh::lean_dec(v___y_5249_);
    crate::leanh::lean_dec_ref(v___y_5248_);
    crate::leanh::lean_dec(v___y_5247_);
    return v_res_5256_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(
    mut v_pre_5257_: *mut crate::leanh::LeanObject,
    mut v_post_5258_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5259_: u8,
    mut v_skipConstInApp_5260_: u8,
    mut v_skipInstances_5261_: u8,
    mut v_fvars_5262_: *mut crate::leanh::LeanObject,
    mut v_e_5263_: *mut crate::leanh::LeanObject,
    mut v_a_5264_: *mut crate::leanh::LeanObject,
    mut v___y_5265_: *mut crate::leanh::LeanObject,
    mut v___y_5266_: *mut crate::leanh::LeanObject,
    mut v___y_5267_: *mut crate::leanh::LeanObject,
    mut v___y_5268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_5263_) == 8 {
        let mut v_declName_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_type_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_nondep_5274_: u8 = 0;
        let mut v___x_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_declName_5270_ = crate::leanh::lean_ctor_get(v_e_5263_, 0);
        crate::leanh::lean_inc(v_declName_5270_);
        v_type_5271_ = crate::leanh::lean_ctor_get(v_e_5263_, 1);
        crate::leanh::lean_inc_ref(v_type_5271_);
        v_value_5272_ = crate::leanh::lean_ctor_get(v_e_5263_, 2);
        crate::leanh::lean_inc_ref(v_value_5272_);
        v_body_5273_ = crate::leanh::lean_ctor_get(v_e_5263_, 3);
        crate::leanh::lean_inc_ref(v_body_5273_);
        v_nondep_5274_ = crate::leanh::lean_ctor_get_uint8(
            v_e_5263_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
        );
        crate::leanh::lean_dec_ref_known(v_e_5263_, 4);
        v___x_5275_ = lean_expr_instantiate_rev(v_type_5271_, v_fvars_5262_);
        crate::leanh::lean_dec_ref(v_type_5271_);
        crate::leanh::lean_inc_ref(v_post_5258_);
        crate::leanh::lean_inc_ref(v_pre_5257_);
        v___x_5276_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_5257_, v_post_5258_, v_usedLetOnly_5259_, v_skipConstInApp_5260_, v_skipInstances_5261_, v___x_5275_, v_a_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_);
        if crate::leanh::lean_obj_tag(v___x_5276_) == 0 {
            let mut v_a_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_5277_ = crate::leanh::lean_ctor_get(v___x_5276_, 0);
            crate::leanh::lean_inc(v_a_5277_);
            crate::leanh::lean_dec_ref_known(v___x_5276_, 1);
            v___x_5278_ = lean_expr_instantiate_rev(v_value_5272_, v_fvars_5262_);
            crate::leanh::lean_dec_ref(v_value_5272_);
            crate::leanh::lean_inc_ref(v_post_5258_);
            crate::leanh::lean_inc_ref(v_pre_5257_);
            v___x_5279_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_5257_, v_post_5258_, v_usedLetOnly_5259_, v_skipConstInApp_5260_, v_skipInstances_5261_, v___x_5278_, v_a_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_);
            if crate::leanh::lean_obj_tag(v___x_5279_) == 0 {
                let mut v_a_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5285_: u8 = 0;
                let mut v___x_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_5280_ = crate::leanh::lean_ctor_get(v___x_5279_, 0);
                crate::leanh::lean_inc(v_a_5280_);
                crate::leanh::lean_dec_ref_known(v___x_5279_, 1);
                v___x_5281_ = crate::leanh::lean_box((v_usedLetOnly_5259_) as usize);
                v___x_5282_ = crate::leanh::lean_box((v_skipConstInApp_5260_) as usize);
                v___x_5283_ = crate::leanh::lean_box((v_skipInstances_5261_) as usize);
                v___f_5284_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed as *mut core::ffi::c_void, 14, 7);
                crate::leanh::lean_closure_set(v___f_5284_, 0, v_fvars_5262_);
                crate::leanh::lean_closure_set(v___f_5284_, 1, v_pre_5257_);
                crate::leanh::lean_closure_set(v___f_5284_, 2, v_post_5258_);
                crate::leanh::lean_closure_set(v___f_5284_, 3, v___x_5281_);
                crate::leanh::lean_closure_set(v___f_5284_, 4, v___x_5282_);
                crate::leanh::lean_closure_set(v___f_5284_, 5, v___x_5283_);
                crate::leanh::lean_closure_set(v___f_5284_, 6, v_body_5273_);
                v___x_5285_ = 0;
                v___x_5286_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_5270_, v_a_5277_, v_a_5280_, v___f_5284_, v_nondep_5274_, v___x_5285_, v_a_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_);
                return v___x_5286_;
            } else {
                crate::leanh::lean_dec(v_a_5277_);
                crate::leanh::lean_dec_ref(v_body_5273_);
                crate::leanh::lean_dec(v_declName_5270_);
                crate::leanh::lean_dec_ref(v_fvars_5262_);
                crate::leanh::lean_dec_ref(v_post_5258_);
                crate::leanh::lean_dec_ref(v_pre_5257_);
                return v___x_5279_;
            }
        } else {
            crate::leanh::lean_dec_ref(v_body_5273_);
            crate::leanh::lean_dec_ref(v_value_5272_);
            crate::leanh::lean_dec(v_declName_5270_);
            crate::leanh::lean_dec_ref(v_fvars_5262_);
            crate::leanh::lean_dec_ref(v_post_5258_);
            crate::leanh::lean_dec_ref(v_pre_5257_);
            return v___x_5276_;
        }
    } else {
        let mut v___x_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5287_ = lean_expr_instantiate_rev(v_e_5263_, v_fvars_5262_);
        crate::leanh::lean_dec_ref(v_e_5263_);
        crate::leanh::lean_inc_ref(v_post_5258_);
        crate::leanh::lean_inc_ref(v_pre_5257_);
        v___x_5288_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_5257_, v_post_5258_, v_usedLetOnly_5259_, v_skipConstInApp_5260_, v_skipInstances_5261_, v___x_5287_, v_a_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_);
        if crate::leanh::lean_obj_tag(v___x_5288_) == 0 {
            let mut v_a_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5290_: u8 = 0;
            let mut v___x_5291_: u8 = 0;
            let mut v___x_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_5289_ = crate::leanh::lean_ctor_get(v___x_5288_, 0);
            crate::leanh::lean_inc(v_a_5289_);
            crate::leanh::lean_dec_ref_known(v___x_5288_, 1);
            v___x_5290_ = 0;
            v___x_5291_ = 1;
            v___x_5292_ = l_Lean_Meta_mkLetFVars(
                v_fvars_5262_,
                v_a_5289_,
                v_usedLetOnly_5259_,
                v___x_5290_,
                v___x_5291_,
                v___y_5265_,
                v___y_5266_,
                v___y_5267_,
                v___y_5268_,
            );
            crate::leanh::lean_dec_ref(v_fvars_5262_);
            if crate::leanh::lean_obj_tag(v___x_5292_) == 0 {
                let mut v_a_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_5293_ = crate::leanh::lean_ctor_get(v___x_5292_, 0);
                crate::leanh::lean_inc(v_a_5293_);
                crate::leanh::lean_dec_ref_known(v___x_5292_, 1);
                v___x_5294_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_5257_, v_post_5258_, v_usedLetOnly_5259_, v_skipConstInApp_5260_, v_skipInstances_5261_, v_a_5293_, v_a_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_);
                return v___x_5294_;
            } else {
                crate::leanh::lean_dec_ref(v_post_5258_);
                crate::leanh::lean_dec_ref(v_pre_5257_);
                return v___x_5292_;
            }
        } else {
            crate::leanh::lean_dec_ref(v_fvars_5262_);
            crate::leanh::lean_dec_ref(v_post_5258_);
            crate::leanh::lean_dec_ref(v_pre_5257_);
            return v___x_5288_;
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5295_ = crate::leanh::lean_box(0);
    v_dummy_5296_ = l_Lean_Expr_sort___override(v___x_5295_);
    return v_dummy_5296_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(
    mut v_pre_5297_: *mut crate::leanh::LeanObject,
    mut v_post_5298_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5299_: u8,
    mut v_skipConstInApp_5300_: u8,
    mut v_skipInstances_5301_: u8,
    mut v_sz_5302_: usize,
    mut v_i_5303_: usize,
    mut v_bs_5304_: *mut crate::leanh::LeanObject,
    mut v___y_5305_: *mut crate::leanh::LeanObject,
    mut v___y_5306_: *mut crate::leanh::LeanObject,
    mut v___y_5307_: *mut crate::leanh::LeanObject,
    mut v___y_5308_: *mut crate::leanh::LeanObject,
    mut v___y_5309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5311_: u8 = 0;
    let mut v___x_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: usize = 0;
    let mut v___x_5319_: usize = 0;
    let mut v___x_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5325_: u8 = 0;
    let mut v___x_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5329_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5311_ = lean_usize_dec_lt(v_i_5303_, v_sz_5302_);
                if v___x_5311_ == 0 {
                    crate::leanh::lean_dec_ref(v_post_5298_);
                    crate::leanh::lean_dec_ref(v_pre_5297_);
                    v___x_5312_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5312_, 0, v_bs_5304_);
                    return v___x_5312_;
                } else {
                    v_v_5313_ = lean_array_uget_borrowed(v_bs_5304_, v_i_5303_);
                    crate::leanh::lean_inc(v_v_5313_);
                    crate::leanh::lean_inc_ref(v_post_5298_);
                    crate::leanh::lean_inc_ref(v_pre_5297_);
                    v___x_5314_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_5297_, v_post_5298_, v_usedLetOnly_5299_, v_skipConstInApp_5300_, v_skipInstances_5301_, v_v_5313_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_);
                    if crate::leanh::lean_obj_tag(v___x_5314_) == 0 {
                        v_a_5315_ = crate::leanh::lean_ctor_get(v___x_5314_, 0);
                        crate::leanh::lean_inc(v_a_5315_);
                        crate::leanh::lean_dec_ref_known(v___x_5314_, 1);
                        v___x_5316_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_5317_ = lean_array_uset(v_bs_5304_, v_i_5303_, v___x_5316_);
                        v___x_5318_ = 1usize;
                        v___x_5319_ = lean_usize_add(v_i_5303_, v___x_5318_);
                        v___x_5320_ = lean_array_uset(v_bs_x27_5317_, v_i_5303_, v_a_5315_);
                        v_i_5303_ = v___x_5319_;
                        v_bs_5304_ = v___x_5320_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_5304_);
                        crate::leanh::lean_dec_ref(v_post_5298_);
                        crate::leanh::lean_dec_ref(v_pre_5297_);
                        v_a_5322_ = crate::leanh::lean_ctor_get(v___x_5314_, 0);
                        v_isSharedCheck_5329_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5314_)) as u8;
                        if v_isSharedCheck_5329_ == 0 {
                            v___x_5324_ = v___x_5314_;
                            v_isShared_5325_ = v_isSharedCheck_5329_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5322_);
                            crate::leanh::lean_dec(v___x_5314_);
                            v___x_5324_ = crate::leanh::lean_box(0);
                            v_isShared_5325_ = v_isSharedCheck_5329_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5325_ == 0 {
                    v___x_5327_ = v___x_5324_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5328_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5328_, 0, v_a_5322_);
                    v___x_5327_ = v_reuseFailAlloc_5328_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5327_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0(
    mut v_pre_5330_: *mut crate::leanh::LeanObject,
    mut v_post_5331_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5332_: u8,
    mut v_skipConstInApp_5333_: u8,
    mut v_skipInstances_5334_: u8,
    mut v___x_5335_: *mut crate::leanh::LeanObject,
    mut v___y_5336_: *mut crate::leanh::LeanObject,
    mut v_b_5337_: *mut crate::leanh::LeanObject,
    mut v_a_5338_: *mut crate::leanh::LeanObject,
    mut v___y_5339_: *mut crate::leanh::LeanObject,
    mut v___y_5340_: *mut crate::leanh::LeanObject,
    mut v___y_5341_: *mut crate::leanh::LeanObject,
    mut v___y_5342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5348_: u8 = 0;
    let mut v___x_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5354_: u8 = 0;
    let mut v_a_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5358_: u8 = 0;
    let mut v___x_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5362_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5344_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_5330_, v_post_5331_, v_usedLetOnly_5332_, v_skipConstInApp_5333_, v_skipInstances_5334_, v___x_5335_, v___y_5336_, v___y_5339_, v___y_5340_, v___y_5341_, v___y_5342_);
                if crate::leanh::lean_obj_tag(v___x_5344_) == 0 {
                    v_a_5345_ = crate::leanh::lean_ctor_get(v___x_5344_, 0);
                    v_isSharedCheck_5354_ = (!crate::leanh::lean_is_exclusive(v___x_5344_)) as u8;
                    if v_isSharedCheck_5354_ == 0 {
                        v___x_5347_ = v___x_5344_;
                        v_isShared_5348_ = v_isSharedCheck_5354_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5345_);
                        crate::leanh::lean_dec(v___x_5344_);
                        v___x_5347_ = crate::leanh::lean_box(0);
                        v_isShared_5348_ = v_isSharedCheck_5354_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_5337_);
                    v_a_5355_ = crate::leanh::lean_ctor_get(v___x_5344_, 0);
                    v_isSharedCheck_5362_ = (!crate::leanh::lean_is_exclusive(v___x_5344_)) as u8;
                    if v_isSharedCheck_5362_ == 0 {
                        v___x_5357_ = v___x_5344_;
                        v_isShared_5358_ = v_isSharedCheck_5362_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5355_);
                        crate::leanh::lean_dec(v___x_5344_);
                        v___x_5357_ = crate::leanh::lean_box(0);
                        v_isShared_5358_ = v_isSharedCheck_5362_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5349_ = lean_array_fset(v_b_5337_, v_a_5338_, v_a_5345_);
                v___x_5350_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5350_, 0, v___x_5349_);
                if v_isShared_5348_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5347_, 0, v___x_5350_);
                    v___x_5352_ = v___x_5347_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5353_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5353_, 0, v___x_5350_);
                    v___x_5352_ = v_reuseFailAlloc_5353_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5352_;
            }
            3 => {
                if v_isShared_5358_ == 0 {
                    v___x_5360_ = v___x_5357_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5361_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5361_, 0, v_a_5355_);
                    v___x_5360_ = v_reuseFailAlloc_5361_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5360_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed(
    mut v_pre_5363_: *mut crate::leanh::LeanObject,
    mut v_post_5364_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5365_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_5366_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_5367_: *mut crate::leanh::LeanObject,
    mut v___x_5368_: *mut crate::leanh::LeanObject,
    mut v___y_5369_: *mut crate::leanh::LeanObject,
    mut v_b_5370_: *mut crate::leanh::LeanObject,
    mut v_a_5371_: *mut crate::leanh::LeanObject,
    mut v___y_5372_: *mut crate::leanh::LeanObject,
    mut v___y_5373_: *mut crate::leanh::LeanObject,
    mut v___y_5374_: *mut crate::leanh::LeanObject,
    mut v___y_5375_: *mut crate::leanh::LeanObject,
    mut v___y_5376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_5377_: u8 = 0;
    let mut v_skipConstInApp_boxed_5378_: u8 = 0;
    let mut v_skipInstances_boxed_5379_: u8 = 0;
    let mut v_res_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_5377_ = (crate::leanh::lean_unbox(v_usedLetOnly_5365_) as u8);
    v_skipConstInApp_boxed_5378_ = (crate::leanh::lean_unbox(v_skipConstInApp_5366_) as u8);
    v_skipInstances_boxed_5379_ = (crate::leanh::lean_unbox(v_skipInstances_5367_) as u8);
    v_res_5380_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0(v_pre_5363_, v_post_5364_, v_usedLetOnly_boxed_5377_, v_skipConstInApp_boxed_5378_, v_skipInstances_boxed_5379_, v___x_5368_, v___y_5369_, v_b_5370_, v_a_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_);
    crate::leanh::lean_dec(v___y_5375_);
    crate::leanh::lean_dec_ref(v___y_5374_);
    crate::leanh::lean_dec(v___y_5373_);
    crate::leanh::lean_dec_ref(v___y_5372_);
    crate::leanh::lean_dec(v_a_5371_);
    crate::leanh::lean_dec(v___y_5369_);
    return v_res_5380_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(
    mut v_upperBound_5381_: *mut crate::leanh::LeanObject,
    mut v___x_5382_: *mut crate::leanh::LeanObject,
    mut v_pre_5383_: *mut crate::leanh::LeanObject,
    mut v_post_5384_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5385_: u8,
    mut v_skipConstInApp_5386_: u8,
    mut v_skipInstances_5387_: u8,
    mut v_a_5388_: *mut crate::leanh::LeanObject,
    mut v_b_5389_: *mut crate::leanh::LeanObject,
    mut v___y_5390_: *mut crate::leanh::LeanObject,
    mut v___y_5391_: *mut crate::leanh::LeanObject,
    mut v___y_5392_: *mut crate::leanh::LeanObject,
    mut v___y_5393_: *mut crate::leanh::LeanObject,
    mut v___y_5394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5402_: u8 = 0;
    let mut v_a_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5411_: u8 = 0;
    let mut v_a_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5415_: u8 = 0;
    let mut v___x_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5419_: u8 = 0;
    let mut v___x_5420_: u8 = 0;
    let mut v___x_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: u8 = 0;
    let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInstance_5430_: u8 = 0;
    let mut v___x_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5420_ = lean_nat_dec_lt(v_a_5388_, v_upperBound_5381_);
                if v___x_5420_ == 0 {
                    crate::leanh::lean_dec(v_a_5388_);
                    crate::leanh::lean_dec_ref(v_post_5384_);
                    crate::leanh::lean_dec_ref(v_pre_5383_);
                    v___x_5421_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5421_, 0, v_b_5389_);
                    return v___x_5421_;
                } else {
                    v___x_5422_ = lean_array_fget_borrowed(v_b_5389_, v_a_5388_);
                    v___x_5423_ = lean_array_get_size(v___x_5382_);
                    v___x_5424_ = lean_nat_dec_lt(v_a_5388_, v___x_5423_);
                    if v___x_5424_ == 0 {
                        crate::leanh::lean_inc(v___x_5422_);
                        v___x_5425_ = crate::leanh::lean_box((v_usedLetOnly_5385_) as usize);
                        v___x_5426_ = crate::leanh::lean_box((v_skipConstInApp_5386_) as usize);
                        v___x_5427_ = crate::leanh::lean_box((v_skipInstances_5387_) as usize);
                        crate::leanh::lean_inc(v_a_5388_);
                        crate::leanh::lean_inc(v___y_5390_);
                        crate::leanh::lean_inc_ref(v_post_5384_);
                        crate::leanh::lean_inc_ref(v_pre_5383_);
                        v___f_5428_ = crate::leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 9);
                        crate::leanh::lean_closure_set(v___f_5428_, 0, v_pre_5383_);
                        crate::leanh::lean_closure_set(v___f_5428_, 1, v_post_5384_);
                        crate::leanh::lean_closure_set(v___f_5428_, 2, v___x_5425_);
                        crate::leanh::lean_closure_set(v___f_5428_, 3, v___x_5426_);
                        crate::leanh::lean_closure_set(v___f_5428_, 4, v___x_5427_);
                        crate::leanh::lean_closure_set(v___f_5428_, 5, v___x_5422_);
                        crate::leanh::lean_closure_set(v___f_5428_, 6, v___y_5390_);
                        crate::leanh::lean_closure_set(v___f_5428_, 7, v_b_5389_);
                        crate::leanh::lean_closure_set(v___f_5428_, 8, v_a_5388_);
                        v___y_5397_ = v___f_5428_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5429_ = lean_array_fget_borrowed(v___x_5382_, v_a_5388_);
                        v_isInstance_5430_ = crate::leanh::lean_ctor_get_uint8(
                            v___x_5429_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 4) as u32,
                        );
                        if v_isInstance_5430_ == 0 {
                            crate::leanh::lean_inc(v___x_5422_);
                            v___x_5431_ = crate::leanh::lean_box((v_usedLetOnly_5385_) as usize);
                            v___x_5432_ = crate::leanh::lean_box((v_skipConstInApp_5386_) as usize);
                            v___x_5433_ = crate::leanh::lean_box((v_skipInstances_5387_) as usize);
                            crate::leanh::lean_inc(v_a_5388_);
                            crate::leanh::lean_inc(v___y_5390_);
                            crate::leanh::lean_inc_ref(v_post_5384_);
                            crate::leanh::lean_inc_ref(v_pre_5383_);
                            v___f_5434_ = crate::leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 9);
                            crate::leanh::lean_closure_set(v___f_5434_, 0, v_pre_5383_);
                            crate::leanh::lean_closure_set(v___f_5434_, 1, v_post_5384_);
                            crate::leanh::lean_closure_set(v___f_5434_, 2, v___x_5431_);
                            crate::leanh::lean_closure_set(v___f_5434_, 3, v___x_5432_);
                            crate::leanh::lean_closure_set(v___f_5434_, 4, v___x_5433_);
                            crate::leanh::lean_closure_set(v___f_5434_, 5, v___x_5422_);
                            crate::leanh::lean_closure_set(v___f_5434_, 6, v___y_5390_);
                            crate::leanh::lean_closure_set(v___f_5434_, 7, v_b_5389_);
                            crate::leanh::lean_closure_set(v___f_5434_, 8, v_a_5388_);
                            v___y_5397_ = v___f_5434_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5435_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5435_, 0, v_b_5389_);
                            v___f_5436_ = crate::leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2___boxed as *mut core::ffi::c_void, 6, 1);
                            crate::leanh::lean_closure_set(v___f_5436_, 0, v___x_5435_);
                            v___y_5397_ = v___f_5436_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_5394_);
                crate::leanh::lean_inc_ref(v___y_5393_);
                crate::leanh::lean_inc(v___y_5392_);
                crate::leanh::lean_inc_ref(v___y_5391_);
                v___x_5398_ = crate::leanh::lean_apply_5(
                    v___y_5397_,
                    v___y_5391_,
                    v___y_5392_,
                    v___y_5393_,
                    v___y_5394_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5398_) == 0 {
                    v_a_5399_ = crate::leanh::lean_ctor_get(v___x_5398_, 0);
                    v_isSharedCheck_5411_ = (!crate::leanh::lean_is_exclusive(v___x_5398_)) as u8;
                    if v_isSharedCheck_5411_ == 0 {
                        v___x_5401_ = v___x_5398_;
                        v_isShared_5402_ = v_isSharedCheck_5411_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5399_);
                        crate::leanh::lean_dec(v___x_5398_);
                        v___x_5401_ = crate::leanh::lean_box(0);
                        v_isShared_5402_ = v_isSharedCheck_5411_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5388_);
                    crate::leanh::lean_dec_ref(v_post_5384_);
                    crate::leanh::lean_dec_ref(v_pre_5383_);
                    v_a_5412_ = crate::leanh::lean_ctor_get(v___x_5398_, 0);
                    v_isSharedCheck_5419_ = (!crate::leanh::lean_is_exclusive(v___x_5398_)) as u8;
                    if v_isSharedCheck_5419_ == 0 {
                        v___x_5414_ = v___x_5398_;
                        v_isShared_5415_ = v_isSharedCheck_5419_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5412_);
                        crate::leanh::lean_dec(v___x_5398_);
                        v___x_5414_ = crate::leanh::lean_box(0);
                        v_isShared_5415_ = v_isSharedCheck_5419_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_5399_) == 0 {
                    crate::leanh::lean_dec(v_a_5388_);
                    crate::leanh::lean_dec_ref(v_post_5384_);
                    crate::leanh::lean_dec_ref(v_pre_5383_);
                    v_a_5403_ = crate::leanh::lean_ctor_get(v_a_5399_, 0);
                    crate::leanh::lean_inc(v_a_5403_);
                    crate::leanh::lean_dec_ref_known(v_a_5399_, 1);
                    if v_isShared_5402_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5401_, 0, v_a_5403_);
                        v___x_5405_ = v___x_5401_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5406_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5406_, 0, v_a_5403_);
                        v___x_5405_ = v_reuseFailAlloc_5406_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5401_);
                    v_a_5407_ = crate::leanh::lean_ctor_get(v_a_5399_, 0);
                    crate::leanh::lean_inc(v_a_5407_);
                    crate::leanh::lean_dec_ref_known(v_a_5399_, 1);
                    v___x_5408_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5409_ = lean_nat_add(v_a_5388_, v___x_5408_);
                    crate::leanh::lean_dec(v_a_5388_);
                    v_a_5388_ = v___x_5409_;
                    v_b_5389_ = v_a_5407_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_5405_;
            }
            4 => {
                if v_isShared_5415_ == 0 {
                    v___x_5417_ = v___x_5414_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5418_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5418_, 0, v_a_5412_);
                    v___x_5417_ = v_reuseFailAlloc_5418_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5417_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(
    mut v_skipInstances_5437_: u8,
    mut v_pre_5438_: *mut crate::leanh::LeanObject,
    mut v_post_5439_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5440_: u8,
    mut v_skipConstInApp_5441_: u8,
    mut v_x_5442_: *mut crate::leanh::LeanObject,
    mut v_x_5443_: *mut crate::leanh::LeanObject,
    mut v_x_5444_: *mut crate::leanh::LeanObject,
    mut v___y_5445_: *mut crate::leanh::LeanObject,
    mut v___y_5446_: *mut crate::leanh::LeanObject,
    mut v___y_5447_: *mut crate::leanh::LeanObject,
    mut v___y_5448_: *mut crate::leanh::LeanObject,
    mut v___y_5449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_f_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5458_: usize = 0;
    let mut v___x_5459_: usize = 0;
    let mut v___x_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5467_: u8 = 0;
    let mut v___x_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5471_: u8 = 0;
    let mut v___x_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramInfo_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5484_: u8 = 0;
    let mut v___x_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5488_: u8 = 0;
    let mut v_a_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5492_: u8 = 0;
    let mut v___x_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5496_: u8 = 0;
    let mut v___x_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5442_) == 5 {
                    v_fn_5500_ = crate::leanh::lean_ctor_get(v_x_5442_, 0);
                    crate::leanh::lean_inc_ref(v_fn_5500_);
                    v_arg_5501_ = crate::leanh::lean_ctor_get(v_x_5442_, 1);
                    crate::leanh::lean_inc_ref(v_arg_5501_);
                    crate::leanh::lean_dec_ref_known(v_x_5442_, 2);
                    v___x_5502_ = lean_array_set(v_x_5443_, v_x_5444_, v_arg_5501_);
                    v___x_5503_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5504_ = lean_nat_sub(v_x_5444_, v___x_5503_);
                    crate::leanh::lean_dec(v_x_5444_);
                    v_x_5442_ = v_fn_5500_;
                    v_x_5443_ = v___x_5502_;
                    v_x_5444_ = v___x_5504_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_5444_);
                    if v_skipConstInApp_5441_ == 0 {
                        state = 8;
                        continue;
                    } else {
                        v___x_5506_ = l_Lean_Expr_isConst(v_x_5442_);
                        if v___x_5506_ == 0 {
                            state = 8;
                            continue;
                        } else {
                            v_f_5452_ = v_x_5442_;
                            v___y_5453_ = v___y_5445_;
                            v___y_5454_ = v___y_5446_;
                            v___y_5455_ = v___y_5447_;
                            v___y_5456_ = v___y_5448_;
                            v___y_5457_ = v___y_5449_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_skipInstances_5437_ == 0 {
                    v_sz_5458_ = lean_array_size(v_x_5443_);
                    v___x_5459_ = 0usize;
                    crate::leanh::lean_inc_ref(v_post_5439_);
                    crate::leanh::lean_inc_ref(v_pre_5438_);
                    v___x_5460_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(v_pre_5438_, v_post_5439_, v_usedLetOnly_5440_, v_skipConstInApp_5441_, v_skipInstances_5437_, v_sz_5458_, v___x_5459_, v_x_5443_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_);
                    if crate::leanh::lean_obj_tag(v___x_5460_) == 0 {
                        v_a_5461_ = crate::leanh::lean_ctor_get(v___x_5460_, 0);
                        crate::leanh::lean_inc(v_a_5461_);
                        crate::leanh::lean_dec_ref_known(v___x_5460_, 1);
                        v___x_5462_ = l_Lean_mkAppN(v_f_5452_, v_a_5461_);
                        crate::leanh::lean_dec(v_a_5461_);
                        v___x_5463_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_5438_, v_post_5439_, v_usedLetOnly_5440_, v_skipConstInApp_5441_, v_skipInstances_5437_, v___x_5462_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_);
                        return v___x_5463_;
                    } else {
                        crate::leanh::lean_dec_ref(v_f_5452_);
                        crate::leanh::lean_dec_ref(v_post_5439_);
                        crate::leanh::lean_dec_ref(v_pre_5438_);
                        v_a_5464_ = crate::leanh::lean_ctor_get(v___x_5460_, 0);
                        v_isSharedCheck_5471_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5460_)) as u8;
                        if v_isSharedCheck_5471_ == 0 {
                            v___x_5466_ = v___x_5460_;
                            v_isShared_5467_ = v_isSharedCheck_5471_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5464_);
                            crate::leanh::lean_dec(v___x_5460_);
                            v___x_5466_ = crate::leanh::lean_box(0);
                            v_isShared_5467_ = v_isSharedCheck_5471_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_5472_ = lean_array_get_size(v_x_5443_);
                    crate::leanh::lean_inc_ref(v_f_5452_);
                    v___x_5473_ = l_Lean_Meta_getFunInfoNArgs(
                        v_f_5452_,
                        v___x_5472_,
                        v___y_5454_,
                        v___y_5455_,
                        v___y_5456_,
                        v___y_5457_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5473_) == 0 {
                        v_a_5474_ = crate::leanh::lean_ctor_get(v___x_5473_, 0);
                        crate::leanh::lean_inc(v_a_5474_);
                        crate::leanh::lean_dec_ref_known(v___x_5473_, 1);
                        v_paramInfo_5475_ = crate::leanh::lean_ctor_get(v_a_5474_, 0);
                        crate::leanh::lean_inc_ref(v_paramInfo_5475_);
                        crate::leanh::lean_dec(v_a_5474_);
                        v___x_5476_ = crate::leanh::lean_unsigned_to_nat(0);
                        crate::leanh::lean_inc_ref(v_post_5439_);
                        crate::leanh::lean_inc_ref(v_pre_5438_);
                        v___x_5477_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v___x_5472_, v_paramInfo_5475_, v_pre_5438_, v_post_5439_, v_usedLetOnly_5440_, v_skipConstInApp_5441_, v_skipInstances_5437_, v___x_5476_, v_x_5443_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_);
                        crate::leanh::lean_dec_ref(v_paramInfo_5475_);
                        if crate::leanh::lean_obj_tag(v___x_5477_) == 0 {
                            v_a_5478_ = crate::leanh::lean_ctor_get(v___x_5477_, 0);
                            crate::leanh::lean_inc(v_a_5478_);
                            crate::leanh::lean_dec_ref_known(v___x_5477_, 1);
                            v___x_5479_ = l_Lean_mkAppN(v_f_5452_, v_a_5478_);
                            crate::leanh::lean_dec(v_a_5478_);
                            v___x_5480_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_5438_, v_post_5439_, v_usedLetOnly_5440_, v_skipConstInApp_5441_, v_skipInstances_5437_, v___x_5479_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_);
                            return v___x_5480_;
                        } else {
                            crate::leanh::lean_dec_ref(v_f_5452_);
                            crate::leanh::lean_dec_ref(v_post_5439_);
                            crate::leanh::lean_dec_ref(v_pre_5438_);
                            v_a_5481_ = crate::leanh::lean_ctor_get(v___x_5477_, 0);
                            v_isSharedCheck_5488_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5477_)) as u8;
                            if v_isSharedCheck_5488_ == 0 {
                                v___x_5483_ = v___x_5477_;
                                v_isShared_5484_ = v_isSharedCheck_5488_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5481_);
                                crate::leanh::lean_dec(v___x_5477_);
                                v___x_5483_ = crate::leanh::lean_box(0);
                                v_isShared_5484_ = v_isSharedCheck_5488_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_f_5452_);
                        crate::leanh::lean_dec_ref(v_x_5443_);
                        crate::leanh::lean_dec_ref(v_post_5439_);
                        crate::leanh::lean_dec_ref(v_pre_5438_);
                        v_a_5489_ = crate::leanh::lean_ctor_get(v___x_5473_, 0);
                        v_isSharedCheck_5496_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5473_)) as u8;
                        if v_isSharedCheck_5496_ == 0 {
                            v___x_5491_ = v___x_5473_;
                            v_isShared_5492_ = v_isSharedCheck_5496_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5489_);
                            crate::leanh::lean_dec(v___x_5473_);
                            v___x_5491_ = crate::leanh::lean_box(0);
                            v_isShared_5492_ = v_isSharedCheck_5496_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_5467_ == 0 {
                    v___x_5469_ = v___x_5466_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5470_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5470_, 0, v_a_5464_);
                    v___x_5469_ = v_reuseFailAlloc_5470_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5469_;
            }
            4 => {
                if v_isShared_5484_ == 0 {
                    v___x_5486_ = v___x_5483_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5487_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5487_, 0, v_a_5481_);
                    v___x_5486_ = v_reuseFailAlloc_5487_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5486_;
            }
            6 => {
                if v_isShared_5492_ == 0 {
                    v___x_5494_ = v___x_5491_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5495_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5495_, 0, v_a_5489_);
                    v___x_5494_ = v_reuseFailAlloc_5495_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5494_;
            }
            8 => {
                crate::leanh::lean_inc_ref(v_post_5439_);
                crate::leanh::lean_inc_ref(v_pre_5438_);
                v___x_5498_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_5438_, v_post_5439_, v_usedLetOnly_5440_, v_skipConstInApp_5441_, v_skipInstances_5437_, v_x_5442_, v___y_5445_, v___y_5446_, v___y_5447_, v___y_5448_, v___y_5449_);
                if crate::leanh::lean_obj_tag(v___x_5498_) == 0 {
                    v_a_5499_ = crate::leanh::lean_ctor_get(v___x_5498_, 0);
                    crate::leanh::lean_inc(v_a_5499_);
                    crate::leanh::lean_dec_ref_known(v___x_5498_, 1);
                    v_f_5452_ = v_a_5499_;
                    v___y_5453_ = v___y_5445_;
                    v___y_5454_ = v___y_5446_;
                    v___y_5455_ = v___y_5447_;
                    v___y_5456_ = v___y_5448_;
                    v___y_5457_ = v___y_5449_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_x_5443_);
                    crate::leanh::lean_dec_ref(v_post_5439_);
                    crate::leanh::lean_dec_ref(v_pre_5438_);
                    return v___x_5498_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(
    mut v___x_5507_: *mut crate::leanh::LeanObject,
    mut v_pre_5508_: *mut crate::leanh::LeanObject,
    mut v_e_5509_: *mut crate::leanh::LeanObject,
    mut v_post_5510_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5511_: u8,
    mut v_skipConstInApp_5512_: u8,
    mut v_skipInstances_5513_: u8,
    mut v___y_5514_: *mut crate::leanh::LeanObject,
    mut v___y_5515_: *mut crate::leanh::LeanObject,
    mut v___y_5516_: *mut crate::leanh::LeanObject,
    mut v___y_5517_: *mut crate::leanh::LeanObject,
    mut v___y_5518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5525_: u8 = 0;
    let mut v___y_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: usize = 0;
    let mut v___x_5545_: usize = 0;
    let mut v___x_5546_: u8 = 0;
    let mut v___x_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: usize = 0;
    let mut v___x_5556_: usize = 0;
    let mut v___x_5557_: u8 = 0;
    let mut v___x_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5570_: u8 = 0;
    let mut v_a_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5574_: u8 = 0;
    let mut v___x_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5578_: u8 = 0;
    let mut v_a_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5582_: u8 = 0;
    let mut v___x_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5586_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5520_ = l_Lean_Core_checkSystem(v___x_5507_, v___y_5517_, v___y_5518_);
                if crate::leanh::lean_obj_tag(v___x_5520_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5520_, 1);
                    crate::leanh::lean_inc_ref(v_pre_5508_);
                    crate::leanh::lean_inc(v___y_5518_);
                    crate::leanh::lean_inc_ref(v___y_5517_);
                    crate::leanh::lean_inc(v___y_5516_);
                    crate::leanh::lean_inc_ref(v___y_5515_);
                    crate::leanh::lean_inc_ref(v_e_5509_);
                    v___x_5521_ = crate::leanh::lean_apply_6(
                        v_pre_5508_,
                        v_e_5509_,
                        v___y_5515_,
                        v___y_5516_,
                        v___y_5517_,
                        v___y_5518_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5521_) == 0 {
                        v_a_5522_ = crate::leanh::lean_ctor_get(v___x_5521_, 0);
                        v_isSharedCheck_5570_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5521_)) as u8;
                        if v_isSharedCheck_5570_ == 0 {
                            v___x_5524_ = v___x_5521_;
                            v_isShared_5525_ = v_isSharedCheck_5570_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5522_);
                            crate::leanh::lean_dec(v___x_5521_);
                            v___x_5524_ = crate::leanh::lean_box(0);
                            v_isShared_5525_ = v_isSharedCheck_5570_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_post_5510_);
                        crate::leanh::lean_dec_ref(v_e_5509_);
                        crate::leanh::lean_dec_ref(v_pre_5508_);
                        v_a_5571_ = crate::leanh::lean_ctor_get(v___x_5521_, 0);
                        v_isSharedCheck_5578_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5521_)) as u8;
                        if v_isSharedCheck_5578_ == 0 {
                            v___x_5573_ = v___x_5521_;
                            v_isShared_5574_ = v_isSharedCheck_5578_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5571_);
                            crate::leanh::lean_dec(v___x_5521_);
                            v___x_5573_ = crate::leanh::lean_box(0);
                            v_isShared_5574_ = v_isSharedCheck_5578_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_post_5510_);
                    crate::leanh::lean_dec_ref(v_e_5509_);
                    crate::leanh::lean_dec_ref(v_pre_5508_);
                    v_a_5579_ = crate::leanh::lean_ctor_get(v___x_5520_, 0);
                    v_isSharedCheck_5586_ = (!crate::leanh::lean_is_exclusive(v___x_5520_)) as u8;
                    if v_isSharedCheck_5586_ == 0 {
                        v___x_5581_ = v___x_5520_;
                        v_isShared_5582_ = v_isSharedCheck_5586_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5579_);
                        crate::leanh::lean_dec(v___x_5520_);
                        v___x_5581_ = crate::leanh::lean_box(0);
                        v_isShared_5582_ = v_isSharedCheck_5586_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => match crate::leanh::lean_obj_tag(v_a_5522_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_post_5510_);
                    crate::leanh::lean_dec_ref(v_e_5509_);
                    crate::leanh::lean_dec_ref(v_pre_5508_);
                    v_e_5562_ = crate::leanh::lean_ctor_get(v_a_5522_, 0);
                    crate::leanh::lean_inc_ref(v_e_5562_);
                    crate::leanh::lean_dec_ref_known(v_a_5522_, 1);
                    if v_isShared_5525_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5524_, 0, v_e_5562_);
                        v___x_5564_ = v___x_5524_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5565_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5565_, 0, v_e_5562_);
                        v___x_5564_ = v_reuseFailAlloc_5565_;
                        state = 3;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_5524_);
                    crate::leanh::lean_dec_ref(v_e_5509_);
                    v_e_5566_ = crate::leanh::lean_ctor_get(v_a_5522_, 0);
                    crate::leanh::lean_inc_ref(v_e_5566_);
                    crate::leanh::lean_dec_ref_known(v_a_5522_, 1);
                    v___x_5567_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_5508_, v_post_5510_, v_usedLetOnly_5511_, v_skipConstInApp_5512_, v_skipInstances_5513_, v_e_5566_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_);
                    return v___x_5567_;
                }
                _ => {
                    crate::leanh::lean_del_object(v___x_5524_);
                    v_e_x3f_5568_ = crate::leanh::lean_ctor_get(v_a_5522_, 0);
                    crate::leanh::lean_inc(v_e_x3f_5568_);
                    crate::leanh::lean_dec_ref_known(v_a_5522_, 1);
                    if crate::leanh::lean_obj_tag(v_e_x3f_5568_) == 0 {
                        v___y_5527_ = v_e_5509_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_e_5509_);
                        v_val_5569_ = crate::leanh::lean_ctor_get(v_e_x3f_5568_, 0);
                        crate::leanh::lean_inc(v_val_5569_);
                        crate::leanh::lean_dec_ref_known(v_e_x3f_5568_, 1);
                        v___y_5527_ = v_val_5569_;
                        state = 2;
                        continue;
                    }
                }
            },
            2 => match crate::leanh::lean_obj_tag(v___y_5527_) {
                7 => {
                    v___x_5528_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0;
                    v___x_5529_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_5508_, v_post_5510_, v_usedLetOnly_5511_, v_skipConstInApp_5512_, v_skipInstances_5513_, v___x_5528_, v___y_5527_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_);
                    return v___x_5529_;
                }
                6 => {
                    v___x_5530_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0;
                    v___x_5531_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_5508_, v_post_5510_, v_usedLetOnly_5511_, v_skipConstInApp_5512_, v_skipInstances_5513_, v___x_5530_, v___y_5527_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_);
                    return v___x_5531_;
                }
                8 => {
                    v___x_5532_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0;
                    v___x_5533_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_5508_, v_post_5510_, v_usedLetOnly_5511_, v_skipConstInApp_5512_, v_skipInstances_5513_, v___x_5532_, v___y_5527_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_);
                    return v___x_5533_;
                }
                5 => {
                    v_dummy_5534_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1_once), _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1);
                    v_nargs_5535_ = l_Lean_Expr_getAppNumArgs(v___y_5527_);
                    crate::leanh::lean_inc(v_nargs_5535_);
                    v___x_5536_ = lean_mk_array(v_nargs_5535_, v_dummy_5534_);
                    v___x_5537_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5538_ = lean_nat_sub(v_nargs_5535_, v___x_5537_);
                    crate::leanh::lean_dec(v_nargs_5535_);
                    v___x_5539_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(v_skipInstances_5513_, v_pre_5508_, v_post_5510_, v_usedLetOnly_5511_, v_skipConstInApp_5512_, v___y_5527_, v___x_5536_, v___x_5538_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_);
                    return v___x_5539_;
                }
                10 => {
                    v_data_5540_ = crate::leanh::lean_ctor_get(v___y_5527_, 0);
                    v_expr_5541_ = crate::leanh::lean_ctor_get(v___y_5527_, 1);
                    crate::leanh::lean_inc_ref(v_expr_5541_);
                    crate::leanh::lean_inc_ref(v_post_5510_);
                    crate::leanh::lean_inc_ref(v_pre_5508_);
                    v___x_5542_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_5508_, v_post_5510_, v_usedLetOnly_5511_, v_skipConstInApp_5512_, v_skipInstances_5513_, v_expr_5541_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_);
                    if crate::leanh::lean_obj_tag(v___x_5542_) == 0 {
                        v_a_5543_ = crate::leanh::lean_ctor_get(v___x_5542_, 0);
                        crate::leanh::lean_inc(v_a_5543_);
                        crate::leanh::lean_dec_ref_known(v___x_5542_, 1);
                        v___x_5544_ = lean_ptr_addr(v_expr_5541_);
                        v___x_5545_ = lean_ptr_addr(v_a_5543_);
                        v___x_5546_ = lean_usize_dec_eq(v___x_5544_, v___x_5545_);
                        if v___x_5546_ == 0 {
                            crate::leanh::lean_inc(v_data_5540_);
                            crate::leanh::lean_dec_ref_known(v___y_5527_, 2);
                            v___x_5547_ = l_Lean_Expr_mdata___override(v_data_5540_, v_a_5543_);
                            v___x_5548_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_5508_, v_post_5510_, v_usedLetOnly_5511_, v_skipConstInApp_5512_, v_skipInstances_5513_, v___x_5547_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_);
                            return v___x_5548_;
                        } else {
                            crate::leanh::lean_dec(v_a_5543_);
                            v___x_5549_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_5508_, v_post_5510_, v_usedLetOnly_5511_, v_skipConstInApp_5512_, v_skipInstances_5513_, v___y_5527_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_);
                            return v___x_5549_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_5527_, 2);
                        crate::leanh::lean_dec_ref(v_post_5510_);
                        crate::leanh::lean_dec_ref(v_pre_5508_);
                        return v___x_5542_;
                    }
                }
                11 => {
                    v_typeName_5550_ = crate::leanh::lean_ctor_get(v___y_5527_, 0);
                    v_idx_5551_ = crate::leanh::lean_ctor_get(v___y_5527_, 1);
                    v_struct_5552_ = crate::leanh::lean_ctor_get(v___y_5527_, 2);
                    crate::leanh::lean_inc_ref(v_struct_5552_);
                    crate::leanh::lean_inc_ref(v_post_5510_);
                    crate::leanh::lean_inc_ref(v_pre_5508_);
                    v___x_5553_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_5508_, v_post_5510_, v_usedLetOnly_5511_, v_skipConstInApp_5512_, v_skipInstances_5513_, v_struct_5552_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_);
                    if crate::leanh::lean_obj_tag(v___x_5553_) == 0 {
                        v_a_5554_ = crate::leanh::lean_ctor_get(v___x_5553_, 0);
                        crate::leanh::lean_inc(v_a_5554_);
                        crate::leanh::lean_dec_ref_known(v___x_5553_, 1);
                        v___x_5555_ = lean_ptr_addr(v_struct_5552_);
                        v___x_5556_ = lean_ptr_addr(v_a_5554_);
                        v___x_5557_ = lean_usize_dec_eq(v___x_5555_, v___x_5556_);
                        if v___x_5557_ == 0 {
                            crate::leanh::lean_inc(v_idx_5551_);
                            crate::leanh::lean_inc(v_typeName_5550_);
                            crate::leanh::lean_dec_ref_known(v___y_5527_, 3);
                            v___x_5558_ = l_Lean_Expr_proj___override(
                                v_typeName_5550_,
                                v_idx_5551_,
                                v_a_5554_,
                            );
                            v___x_5559_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_5508_, v_post_5510_, v_usedLetOnly_5511_, v_skipConstInApp_5512_, v_skipInstances_5513_, v___x_5558_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_);
                            return v___x_5559_;
                        } else {
                            crate::leanh::lean_dec(v_a_5554_);
                            v___x_5560_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_5508_, v_post_5510_, v_usedLetOnly_5511_, v_skipConstInApp_5512_, v_skipInstances_5513_, v___y_5527_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_);
                            return v___x_5560_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_5527_, 3);
                        crate::leanh::lean_dec_ref(v_post_5510_);
                        crate::leanh::lean_dec_ref(v_pre_5508_);
                        return v___x_5553_;
                    }
                }
                _ => {
                    v___x_5561_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_5508_, v_post_5510_, v_usedLetOnly_5511_, v_skipConstInApp_5512_, v_skipInstances_5513_, v___y_5527_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_);
                    return v___x_5561_;
                }
            },
            3 => {
                return v___x_5564_;
            }
            4 => {
                if v_isShared_5574_ == 0 {
                    v___x_5576_ = v___x_5573_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5577_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5577_, 0, v_a_5571_);
                    v___x_5576_ = v_reuseFailAlloc_5577_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5576_;
            }
            6 => {
                if v_isShared_5582_ == 0 {
                    v___x_5584_ = v___x_5581_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5585_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5585_, 0, v_a_5579_);
                    v___x_5584_ = v_reuseFailAlloc_5585_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5584_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed(
    mut v___x_5587_: *mut crate::leanh::LeanObject,
    mut v_pre_5588_: *mut crate::leanh::LeanObject,
    mut v_e_5589_: *mut crate::leanh::LeanObject,
    mut v_post_5590_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5591_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_5592_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_5593_: *mut crate::leanh::LeanObject,
    mut v___y_5594_: *mut crate::leanh::LeanObject,
    mut v___y_5595_: *mut crate::leanh::LeanObject,
    mut v___y_5596_: *mut crate::leanh::LeanObject,
    mut v___y_5597_: *mut crate::leanh::LeanObject,
    mut v___y_5598_: *mut crate::leanh::LeanObject,
    mut v___y_5599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_5600_: u8 = 0;
    let mut v_skipConstInApp_boxed_5601_: u8 = 0;
    let mut v_skipInstances_boxed_5602_: u8 = 0;
    let mut v_res_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_5600_ = (crate::leanh::lean_unbox(v_usedLetOnly_5591_) as u8);
    v_skipConstInApp_boxed_5601_ = (crate::leanh::lean_unbox(v_skipConstInApp_5592_) as u8);
    v_skipInstances_boxed_5602_ = (crate::leanh::lean_unbox(v_skipInstances_5593_) as u8);
    v_res_5603_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(v___x_5587_, v_pre_5588_, v_e_5589_, v_post_5590_, v_usedLetOnly_boxed_5600_, v_skipConstInApp_boxed_5601_, v_skipInstances_boxed_5602_, v___y_5594_, v___y_5595_, v___y_5596_, v___y_5597_, v___y_5598_);
    crate::leanh::lean_dec(v___y_5598_);
    crate::leanh::lean_dec_ref(v___y_5597_);
    crate::leanh::lean_dec(v___y_5596_);
    crate::leanh::lean_dec_ref(v___y_5595_);
    crate::leanh::lean_dec(v___y_5594_);
    return v_res_5603_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(
    mut v_pre_5604_: *mut crate::leanh::LeanObject,
    mut v_post_5605_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5606_: u8,
    mut v_skipConstInApp_5607_: u8,
    mut v_skipInstances_5608_: u8,
    mut v_e_5609_: *mut crate::leanh::LeanObject,
    mut v_a_5610_: *mut crate::leanh::LeanObject,
    mut v___y_5611_: *mut crate::leanh::LeanObject,
    mut v___y_5612_: *mut crate::leanh::LeanObject,
    mut v___y_5613_: *mut crate::leanh::LeanObject,
    mut v___y_5614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5621_: u8 = 0;
    let mut v___x_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5634_: u8 = 0;
    let mut v___x_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5638_: u8 = 0;
    let mut v_unused_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5643_: u8 = 0;
    let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5647_: u8 = 0;
    let mut v_val_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5652_: u8 = 0;
    let mut v_a_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5656_: u8 = 0;
    let mut v___x_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5660_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_5610_);
                v___x_5616_ = crate::leanh::lean_alloc_closure(
                    l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_5616_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_5616_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_5616_, 2, v_a_5610_);
                v___x_5617_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(crate::leanh::lean_box(0), v___x_5616_, v___y_5611_, v___y_5612_, v___y_5613_, v___y_5614_);
                if crate::leanh::lean_obj_tag(v___x_5617_) == 0 {
                    v_a_5618_ = crate::leanh::lean_ctor_get(v___x_5617_, 0);
                    v_isSharedCheck_5652_ = (!crate::leanh::lean_is_exclusive(v___x_5617_)) as u8;
                    if v_isSharedCheck_5652_ == 0 {
                        v___x_5620_ = v___x_5617_;
                        v_isShared_5621_ = v_isSharedCheck_5652_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5618_);
                        crate::leanh::lean_dec(v___x_5617_);
                        v___x_5620_ = crate::leanh::lean_box(0);
                        v_isShared_5621_ = v_isSharedCheck_5652_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_5609_);
                    crate::leanh::lean_dec_ref(v_post_5605_);
                    crate::leanh::lean_dec_ref(v_pre_5604_);
                    v_a_5653_ = crate::leanh::lean_ctor_get(v___x_5617_, 0);
                    v_isSharedCheck_5660_ = (!crate::leanh::lean_is_exclusive(v___x_5617_)) as u8;
                    if v_isSharedCheck_5660_ == 0 {
                        v___x_5655_ = v___x_5617_;
                        v_isShared_5656_ = v_isSharedCheck_5660_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5653_);
                        crate::leanh::lean_dec(v___x_5617_);
                        v___x_5655_ = crate::leanh::lean_box(0);
                        v_isShared_5656_ = v_isSharedCheck_5660_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5622_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_a_5618_, v_e_5609_);
                crate::leanh::lean_dec(v_a_5618_);
                if crate::leanh::lean_obj_tag(v___x_5622_) == 0 {
                    crate::leanh::lean_del_object(v___x_5620_);
                    v___x_5623_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0;
                    v___x_5624_ = crate::leanh::lean_box((v_usedLetOnly_5606_) as usize);
                    v___x_5625_ = crate::leanh::lean_box((v_skipConstInApp_5607_) as usize);
                    v___x_5626_ = crate::leanh::lean_box((v_skipInstances_5608_) as usize);
                    crate::leanh::lean_inc_ref(v_e_5609_);
                    v___f_5627_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed as *mut core::ffi::c_void, 13, 7);
                    crate::leanh::lean_closure_set(v___f_5627_, 0, v___x_5623_);
                    crate::leanh::lean_closure_set(v___f_5627_, 1, v_pre_5604_);
                    crate::leanh::lean_closure_set(v___f_5627_, 2, v_e_5609_);
                    crate::leanh::lean_closure_set(v___f_5627_, 3, v_post_5605_);
                    crate::leanh::lean_closure_set(v___f_5627_, 4, v___x_5624_);
                    crate::leanh::lean_closure_set(v___f_5627_, 5, v___x_5625_);
                    crate::leanh::lean_closure_set(v___f_5627_, 6, v___x_5626_);
                    v___x_5628_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v___f_5627_, v_a_5610_, v___y_5611_, v___y_5612_, v___y_5613_, v___y_5614_);
                    if crate::leanh::lean_obj_tag(v___x_5628_) == 0 {
                        v_a_5629_ = crate::leanh::lean_ctor_get(v___x_5628_, 0);
                        crate::leanh::lean_inc_n(v_a_5629_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_5628_, 1);
                        crate::leanh::lean_inc(v_a_5610_);
                        v___f_5630_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed as *mut core::ffi::c_void, 4, 3);
                        crate::leanh::lean_closure_set(v___f_5630_, 0, v_a_5610_);
                        crate::leanh::lean_closure_set(v___f_5630_, 1, v_e_5609_);
                        crate::leanh::lean_closure_set(v___f_5630_, 2, v_a_5629_);
                        v___x_5631_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(crate::leanh::lean_box(0), v___f_5630_, v___y_5611_, v___y_5612_, v___y_5613_, v___y_5614_);
                        if crate::leanh::lean_obj_tag(v___x_5631_) == 0 {
                            v_isSharedCheck_5638_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5631_)) as u8;
                            if v_isSharedCheck_5638_ == 0 {
                                v_unused_5639_ = crate::leanh::lean_ctor_get(v___x_5631_, 0);
                                crate::leanh::lean_dec(v_unused_5639_);
                                v___x_5633_ = v___x_5631_;
                                v_isShared_5634_ = v_isSharedCheck_5638_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_5631_);
                                v___x_5633_ = crate::leanh::lean_box(0);
                                v_isShared_5634_ = v_isSharedCheck_5638_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5629_);
                            v_a_5640_ = crate::leanh::lean_ctor_get(v___x_5631_, 0);
                            v_isSharedCheck_5647_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5631_)) as u8;
                            if v_isSharedCheck_5647_ == 0 {
                                v___x_5642_ = v___x_5631_;
                                v_isShared_5643_ = v_isSharedCheck_5647_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5640_);
                                crate::leanh::lean_dec(v___x_5631_);
                                v___x_5642_ = crate::leanh::lean_box(0);
                                v_isShared_5643_ = v_isSharedCheck_5647_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_5609_);
                        return v___x_5628_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_5609_);
                    crate::leanh::lean_dec_ref(v_post_5605_);
                    crate::leanh::lean_dec_ref(v_pre_5604_);
                    v_val_5648_ = crate::leanh::lean_ctor_get(v___x_5622_, 0);
                    crate::leanh::lean_inc(v_val_5648_);
                    crate::leanh::lean_dec_ref_known(v___x_5622_, 1);
                    if v_isShared_5621_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5620_, 0, v_val_5648_);
                        v___x_5650_ = v___x_5620_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_5651_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5651_, 0, v_val_5648_);
                        v___x_5650_ = v_reuseFailAlloc_5651_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5634_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5633_, 0, v_a_5629_);
                    v___x_5636_ = v___x_5633_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5637_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5637_, 0, v_a_5629_);
                    v___x_5636_ = v_reuseFailAlloc_5637_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5636_;
            }
            4 => {
                if v_isShared_5643_ == 0 {
                    v___x_5645_ = v___x_5642_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5646_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5646_, 0, v_a_5640_);
                    v___x_5645_ = v_reuseFailAlloc_5646_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5645_;
            }
            6 => {
                return v___x_5650_;
            }
            7 => {
                if v_isShared_5656_ == 0 {
                    v___x_5658_ = v___x_5655_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5659_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5659_, 0, v_a_5653_);
                    v___x_5658_ = v_reuseFailAlloc_5659_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5658_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed(
    mut v_fvars_5661_: *mut crate::leanh::LeanObject,
    mut v_pre_5662_: *mut crate::leanh::LeanObject,
    mut v_post_5663_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5664_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_5665_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_5666_: *mut crate::leanh::LeanObject,
    mut v_body_5667_: *mut crate::leanh::LeanObject,
    mut v_x_5668_: *mut crate::leanh::LeanObject,
    mut v___y_5669_: *mut crate::leanh::LeanObject,
    mut v___y_5670_: *mut crate::leanh::LeanObject,
    mut v___y_5671_: *mut crate::leanh::LeanObject,
    mut v___y_5672_: *mut crate::leanh::LeanObject,
    mut v___y_5673_: *mut crate::leanh::LeanObject,
    mut v___y_5674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_5675_: u8 = 0;
    let mut v_skipConstInApp_boxed_5676_: u8 = 0;
    let mut v_skipInstances_boxed_5677_: u8 = 0;
    let mut v_res_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_5675_ = (crate::leanh::lean_unbox(v_usedLetOnly_5664_) as u8);
    v_skipConstInApp_boxed_5676_ = (crate::leanh::lean_unbox(v_skipConstInApp_5665_) as u8);
    v_skipInstances_boxed_5677_ = (crate::leanh::lean_unbox(v_skipInstances_5666_) as u8);
    v_res_5678_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(v_fvars_5661_, v_pre_5662_, v_post_5663_, v_usedLetOnly_boxed_5675_, v_skipConstInApp_boxed_5676_, v_skipInstances_boxed_5677_, v_body_5667_, v_x_5668_, v___y_5669_, v___y_5670_, v___y_5671_, v___y_5672_, v___y_5673_);
    crate::leanh::lean_dec(v___y_5673_);
    crate::leanh::lean_dec_ref(v___y_5672_);
    crate::leanh::lean_dec(v___y_5671_);
    crate::leanh::lean_dec_ref(v___y_5670_);
    crate::leanh::lean_dec(v___y_5669_);
    return v_res_5678_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(
    mut v_pre_5679_: *mut crate::leanh::LeanObject,
    mut v_post_5680_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5681_: u8,
    mut v_skipConstInApp_5682_: u8,
    mut v_skipInstances_5683_: u8,
    mut v_fvars_5684_: *mut crate::leanh::LeanObject,
    mut v_e_5685_: *mut crate::leanh::LeanObject,
    mut v_a_5686_: *mut crate::leanh::LeanObject,
    mut v___y_5687_: *mut crate::leanh::LeanObject,
    mut v___y_5688_: *mut crate::leanh::LeanObject,
    mut v___y_5689_: *mut crate::leanh::LeanObject,
    mut v___y_5690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_5685_) == 7 {
        let mut v_binderName_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_5693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_5695_: u8 = 0;
        let mut v___x_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_binderName_5692_ = crate::leanh::lean_ctor_get(v_e_5685_, 0);
        crate::leanh::lean_inc(v_binderName_5692_);
        v_binderType_5693_ = crate::leanh::lean_ctor_get(v_e_5685_, 1);
        crate::leanh::lean_inc_ref(v_binderType_5693_);
        v_body_5694_ = crate::leanh::lean_ctor_get(v_e_5685_, 2);
        crate::leanh::lean_inc_ref(v_body_5694_);
        v_binderInfo_5695_ = crate::leanh::lean_ctor_get_uint8(
            v_e_5685_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        );
        crate::leanh::lean_dec_ref_known(v_e_5685_, 3);
        v___x_5696_ = lean_expr_instantiate_rev(v_binderType_5693_, v_fvars_5684_);
        crate::leanh::lean_dec_ref(v_binderType_5693_);
        crate::leanh::lean_inc_ref(v_post_5680_);
        crate::leanh::lean_inc_ref(v_pre_5679_);
        v___x_5697_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_5679_, v_post_5680_, v_usedLetOnly_5681_, v_skipConstInApp_5682_, v_skipInstances_5683_, v___x_5696_, v_a_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_);
        if crate::leanh::lean_obj_tag(v___x_5697_) == 0 {
            let mut v_a_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5703_: u8 = 0;
            let mut v___x_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_5698_ = crate::leanh::lean_ctor_get(v___x_5697_, 0);
            crate::leanh::lean_inc(v_a_5698_);
            crate::leanh::lean_dec_ref_known(v___x_5697_, 1);
            v___x_5699_ = crate::leanh::lean_box((v_usedLetOnly_5681_) as usize);
            v___x_5700_ = crate::leanh::lean_box((v_skipConstInApp_5682_) as usize);
            v___x_5701_ = crate::leanh::lean_box((v_skipInstances_5683_) as usize);
            v___f_5702_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed as *mut core::ffi::c_void, 14, 7);
            crate::leanh::lean_closure_set(v___f_5702_, 0, v_fvars_5684_);
            crate::leanh::lean_closure_set(v___f_5702_, 1, v_pre_5679_);
            crate::leanh::lean_closure_set(v___f_5702_, 2, v_post_5680_);
            crate::leanh::lean_closure_set(v___f_5702_, 3, v___x_5699_);
            crate::leanh::lean_closure_set(v___f_5702_, 4, v___x_5700_);
            crate::leanh::lean_closure_set(v___f_5702_, 5, v___x_5701_);
            crate::leanh::lean_closure_set(v___f_5702_, 6, v_body_5694_);
            v___x_5703_ = 0;
            v___x_5704_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_5692_, v_binderInfo_5695_, v_a_5698_, v___f_5702_, v___x_5703_, v_a_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_);
            return v___x_5704_;
        } else {
            crate::leanh::lean_dec_ref(v_body_5694_);
            crate::leanh::lean_dec(v_binderName_5692_);
            crate::leanh::lean_dec_ref(v_fvars_5684_);
            crate::leanh::lean_dec_ref(v_post_5680_);
            crate::leanh::lean_dec_ref(v_pre_5679_);
            return v___x_5697_;
        }
    } else {
        let mut v___x_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5705_ = lean_expr_instantiate_rev(v_e_5685_, v_fvars_5684_);
        crate::leanh::lean_dec_ref(v_e_5685_);
        crate::leanh::lean_inc_ref(v_post_5680_);
        crate::leanh::lean_inc_ref(v_pre_5679_);
        v___x_5706_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_5679_, v_post_5680_, v_usedLetOnly_5681_, v_skipConstInApp_5682_, v_skipInstances_5683_, v___x_5705_, v_a_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_);
        if crate::leanh::lean_obj_tag(v___x_5706_) == 0 {
            let mut v_a_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5708_: u8 = 0;
            let mut v___x_5709_: u8 = 0;
            let mut v___x_5710_: u8 = 0;
            let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_5707_ = crate::leanh::lean_ctor_get(v___x_5706_, 0);
            crate::leanh::lean_inc(v_a_5707_);
            crate::leanh::lean_dec_ref_known(v___x_5706_, 1);
            v___x_5708_ = 0;
            v___x_5709_ = 1;
            v___x_5710_ = 1;
            v___x_5711_ = l_Lean_Meta_mkForallFVars(
                v_fvars_5684_,
                v_a_5707_,
                v___x_5708_,
                v_usedLetOnly_5681_,
                v___x_5709_,
                v___x_5710_,
                v___y_5687_,
                v___y_5688_,
                v___y_5689_,
                v___y_5690_,
            );
            crate::leanh::lean_dec_ref(v_fvars_5684_);
            if crate::leanh::lean_obj_tag(v___x_5711_) == 0 {
                let mut v_a_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_5712_ = crate::leanh::lean_ctor_get(v___x_5711_, 0);
                crate::leanh::lean_inc(v_a_5712_);
                crate::leanh::lean_dec_ref_known(v___x_5711_, 1);
                v___x_5713_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_5679_, v_post_5680_, v_usedLetOnly_5681_, v_skipConstInApp_5682_, v_skipInstances_5683_, v_a_5712_, v_a_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_);
                return v___x_5713_;
            } else {
                crate::leanh::lean_dec_ref(v_post_5680_);
                crate::leanh::lean_dec_ref(v_pre_5679_);
                return v___x_5711_;
            }
        } else {
            crate::leanh::lean_dec_ref(v_fvars_5684_);
            crate::leanh::lean_dec_ref(v_post_5680_);
            crate::leanh::lean_dec_ref(v_pre_5679_);
            return v___x_5706_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(
    mut v_fvars_5714_: *mut crate::leanh::LeanObject,
    mut v_pre_5715_: *mut crate::leanh::LeanObject,
    mut v_post_5716_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5717_: u8,
    mut v_skipConstInApp_5718_: u8,
    mut v_skipInstances_5719_: u8,
    mut v_body_5720_: *mut crate::leanh::LeanObject,
    mut v_x_5721_: *mut crate::leanh::LeanObject,
    mut v___y_5722_: *mut crate::leanh::LeanObject,
    mut v___y_5723_: *mut crate::leanh::LeanObject,
    mut v___y_5724_: *mut crate::leanh::LeanObject,
    mut v___y_5725_: *mut crate::leanh::LeanObject,
    mut v___y_5726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5728_ = lean_array_push(v_fvars_5714_, v_x_5721_);
    v___x_5729_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_5715_, v_post_5716_, v_usedLetOnly_5717_, v_skipConstInApp_5718_, v_skipInstances_5719_, v___x_5728_, v_body_5720_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_);
    return v___x_5729_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2___boxed(
    mut v_pre_5730_: *mut crate::leanh::LeanObject,
    mut v_post_5731_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5732_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_5733_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_5734_: *mut crate::leanh::LeanObject,
    mut v_e_5735_: *mut crate::leanh::LeanObject,
    mut v_a_5736_: *mut crate::leanh::LeanObject,
    mut v___y_5737_: *mut crate::leanh::LeanObject,
    mut v___y_5738_: *mut crate::leanh::LeanObject,
    mut v___y_5739_: *mut crate::leanh::LeanObject,
    mut v___y_5740_: *mut crate::leanh::LeanObject,
    mut v___y_5741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_5742_: u8 = 0;
    let mut v_skipConstInApp_boxed_5743_: u8 = 0;
    let mut v_skipInstances_boxed_5744_: u8 = 0;
    let mut v_res_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_5742_ = (crate::leanh::lean_unbox(v_usedLetOnly_5732_) as u8);
    v_skipConstInApp_boxed_5743_ = (crate::leanh::lean_unbox(v_skipConstInApp_5733_) as u8);
    v_skipInstances_boxed_5744_ = (crate::leanh::lean_unbox(v_skipInstances_5734_) as u8);
    v_res_5745_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_5730_, v_post_5731_, v_usedLetOnly_boxed_5742_, v_skipConstInApp_boxed_5743_, v_skipInstances_boxed_5744_, v_e_5735_, v_a_5736_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_);
    crate::leanh::lean_dec(v___y_5740_);
    crate::leanh::lean_dec_ref(v___y_5739_);
    crate::leanh::lean_dec(v___y_5738_);
    crate::leanh::lean_dec_ref(v___y_5737_);
    crate::leanh::lean_dec(v_a_5736_);
    return v_res_5745_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___boxed(
    mut v_pre_5746_: *mut crate::leanh::LeanObject,
    mut v_post_5747_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5748_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_5749_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_5750_: *mut crate::leanh::LeanObject,
    mut v_sz_5751_: *mut crate::leanh::LeanObject,
    mut v_i_5752_: *mut crate::leanh::LeanObject,
    mut v_bs_5753_: *mut crate::leanh::LeanObject,
    mut v___y_5754_: *mut crate::leanh::LeanObject,
    mut v___y_5755_: *mut crate::leanh::LeanObject,
    mut v___y_5756_: *mut crate::leanh::LeanObject,
    mut v___y_5757_: *mut crate::leanh::LeanObject,
    mut v___y_5758_: *mut crate::leanh::LeanObject,
    mut v___y_5759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_5760_: u8 = 0;
    let mut v_skipConstInApp_boxed_5761_: u8 = 0;
    let mut v_skipInstances_boxed_5762_: u8 = 0;
    let mut v_sz_boxed_5763_: usize = 0;
    let mut v_i_boxed_5764_: usize = 0;
    let mut v_res_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_5760_ = (crate::leanh::lean_unbox(v_usedLetOnly_5748_) as u8);
    v_skipConstInApp_boxed_5761_ = (crate::leanh::lean_unbox(v_skipConstInApp_5749_) as u8);
    v_skipInstances_boxed_5762_ = (crate::leanh::lean_unbox(v_skipInstances_5750_) as u8);
    v_sz_boxed_5763_ = crate::leanh::lean_unbox_usize(v_sz_5751_);
    crate::leanh::lean_dec(v_sz_5751_);
    v_i_boxed_5764_ = crate::leanh::lean_unbox_usize(v_i_5752_);
    crate::leanh::lean_dec(v_i_5752_);
    v_res_5765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(v_pre_5746_, v_post_5747_, v_usedLetOnly_boxed_5760_, v_skipConstInApp_boxed_5761_, v_skipInstances_boxed_5762_, v_sz_boxed_5763_, v_i_boxed_5764_, v_bs_5753_, v___y_5754_, v___y_5755_, v___y_5756_, v___y_5757_, v___y_5758_);
    crate::leanh::lean_dec(v___y_5758_);
    crate::leanh::lean_dec_ref(v___y_5757_);
    crate::leanh::lean_dec(v___y_5756_);
    crate::leanh::lean_dec_ref(v___y_5755_);
    crate::leanh::lean_dec(v___y_5754_);
    return v_res_5765_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___boxed(
    mut v_pre_5766_: *mut crate::leanh::LeanObject,
    mut v_post_5767_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5768_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_5769_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_5770_: *mut crate::leanh::LeanObject,
    mut v_e_5771_: *mut crate::leanh::LeanObject,
    mut v_a_5772_: *mut crate::leanh::LeanObject,
    mut v___y_5773_: *mut crate::leanh::LeanObject,
    mut v___y_5774_: *mut crate::leanh::LeanObject,
    mut v___y_5775_: *mut crate::leanh::LeanObject,
    mut v___y_5776_: *mut crate::leanh::LeanObject,
    mut v___y_5777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_5778_: u8 = 0;
    let mut v_skipConstInApp_boxed_5779_: u8 = 0;
    let mut v_skipInstances_boxed_5780_: u8 = 0;
    let mut v_res_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_5778_ = (crate::leanh::lean_unbox(v_usedLetOnly_5768_) as u8);
    v_skipConstInApp_boxed_5779_ = (crate::leanh::lean_unbox(v_skipConstInApp_5769_) as u8);
    v_skipInstances_boxed_5780_ = (crate::leanh::lean_unbox(v_skipInstances_5770_) as u8);
    v_res_5781_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_5766_, v_post_5767_, v_usedLetOnly_boxed_5778_, v_skipConstInApp_boxed_5779_, v_skipInstances_boxed_5780_, v_e_5771_, v_a_5772_, v___y_5773_, v___y_5774_, v___y_5775_, v___y_5776_);
    crate::leanh::lean_dec(v___y_5776_);
    crate::leanh::lean_dec_ref(v___y_5775_);
    crate::leanh::lean_dec(v___y_5774_);
    crate::leanh::lean_dec_ref(v___y_5773_);
    crate::leanh::lean_dec(v_a_5772_);
    return v_res_5781_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___boxed(
    mut v_pre_5782_: *mut crate::leanh::LeanObject,
    mut v_post_5783_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5784_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_5785_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_5786_: *mut crate::leanh::LeanObject,
    mut v_fvars_5787_: *mut crate::leanh::LeanObject,
    mut v_e_5788_: *mut crate::leanh::LeanObject,
    mut v_a_5789_: *mut crate::leanh::LeanObject,
    mut v___y_5790_: *mut crate::leanh::LeanObject,
    mut v___y_5791_: *mut crate::leanh::LeanObject,
    mut v___y_5792_: *mut crate::leanh::LeanObject,
    mut v___y_5793_: *mut crate::leanh::LeanObject,
    mut v___y_5794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_5795_: u8 = 0;
    let mut v_skipConstInApp_boxed_5796_: u8 = 0;
    let mut v_skipInstances_boxed_5797_: u8 = 0;
    let mut v_res_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_5795_ = (crate::leanh::lean_unbox(v_usedLetOnly_5784_) as u8);
    v_skipConstInApp_boxed_5796_ = (crate::leanh::lean_unbox(v_skipConstInApp_5785_) as u8);
    v_skipInstances_boxed_5797_ = (crate::leanh::lean_unbox(v_skipInstances_5786_) as u8);
    v_res_5798_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_5782_, v_post_5783_, v_usedLetOnly_boxed_5795_, v_skipConstInApp_boxed_5796_, v_skipInstances_boxed_5797_, v_fvars_5787_, v_e_5788_, v_a_5789_, v___y_5790_, v___y_5791_, v___y_5792_, v___y_5793_);
    crate::leanh::lean_dec(v___y_5793_);
    crate::leanh::lean_dec_ref(v___y_5792_);
    crate::leanh::lean_dec(v___y_5791_);
    crate::leanh::lean_dec_ref(v___y_5790_);
    crate::leanh::lean_dec(v_a_5789_);
    return v_res_5798_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___boxed(
    mut v_pre_5799_: *mut crate::leanh::LeanObject,
    mut v_post_5800_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5801_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_5802_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_5803_: *mut crate::leanh::LeanObject,
    mut v_fvars_5804_: *mut crate::leanh::LeanObject,
    mut v_e_5805_: *mut crate::leanh::LeanObject,
    mut v_a_5806_: *mut crate::leanh::LeanObject,
    mut v___y_5807_: *mut crate::leanh::LeanObject,
    mut v___y_5808_: *mut crate::leanh::LeanObject,
    mut v___y_5809_: *mut crate::leanh::LeanObject,
    mut v___y_5810_: *mut crate::leanh::LeanObject,
    mut v___y_5811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_5812_: u8 = 0;
    let mut v_skipConstInApp_boxed_5813_: u8 = 0;
    let mut v_skipInstances_boxed_5814_: u8 = 0;
    let mut v_res_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_5812_ = (crate::leanh::lean_unbox(v_usedLetOnly_5801_) as u8);
    v_skipConstInApp_boxed_5813_ = (crate::leanh::lean_unbox(v_skipConstInApp_5802_) as u8);
    v_skipInstances_boxed_5814_ = (crate::leanh::lean_unbox(v_skipInstances_5803_) as u8);
    v_res_5815_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_5799_, v_post_5800_, v_usedLetOnly_boxed_5812_, v_skipConstInApp_boxed_5813_, v_skipInstances_boxed_5814_, v_fvars_5804_, v_e_5805_, v_a_5806_, v___y_5807_, v___y_5808_, v___y_5809_, v___y_5810_);
    crate::leanh::lean_dec(v___y_5810_);
    crate::leanh::lean_dec_ref(v___y_5809_);
    crate::leanh::lean_dec(v___y_5808_);
    crate::leanh::lean_dec_ref(v___y_5807_);
    crate::leanh::lean_dec(v_a_5806_);
    return v_res_5815_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___boxed(
    mut v_pre_5816_: *mut crate::leanh::LeanObject,
    mut v_post_5817_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5818_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_5819_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_5820_: *mut crate::leanh::LeanObject,
    mut v_fvars_5821_: *mut crate::leanh::LeanObject,
    mut v_e_5822_: *mut crate::leanh::LeanObject,
    mut v_a_5823_: *mut crate::leanh::LeanObject,
    mut v___y_5824_: *mut crate::leanh::LeanObject,
    mut v___y_5825_: *mut crate::leanh::LeanObject,
    mut v___y_5826_: *mut crate::leanh::LeanObject,
    mut v___y_5827_: *mut crate::leanh::LeanObject,
    mut v___y_5828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_5829_: u8 = 0;
    let mut v_skipConstInApp_boxed_5830_: u8 = 0;
    let mut v_skipInstances_boxed_5831_: u8 = 0;
    let mut v_res_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_5829_ = (crate::leanh::lean_unbox(v_usedLetOnly_5818_) as u8);
    v_skipConstInApp_boxed_5830_ = (crate::leanh::lean_unbox(v_skipConstInApp_5819_) as u8);
    v_skipInstances_boxed_5831_ = (crate::leanh::lean_unbox(v_skipInstances_5820_) as u8);
    v_res_5832_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_5816_, v_post_5817_, v_usedLetOnly_boxed_5829_, v_skipConstInApp_boxed_5830_, v_skipInstances_boxed_5831_, v_fvars_5821_, v_e_5822_, v_a_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_);
    crate::leanh::lean_dec(v___y_5827_);
    crate::leanh::lean_dec_ref(v___y_5826_);
    crate::leanh::lean_dec(v___y_5825_);
    crate::leanh::lean_dec_ref(v___y_5824_);
    crate::leanh::lean_dec(v_a_5823_);
    return v_res_5832_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_upperBound_5833_: *mut crate::leanh::LeanObject,
    mut v___x_5834_: *mut crate::leanh::LeanObject,
    mut v_pre_5835_: *mut crate::leanh::LeanObject,
    mut v_post_5836_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5837_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_5838_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_5839_: *mut crate::leanh::LeanObject,
    mut v_a_5840_: *mut crate::leanh::LeanObject,
    mut v_b_5841_: *mut crate::leanh::LeanObject,
    mut v___y_5842_: *mut crate::leanh::LeanObject,
    mut v___y_5843_: *mut crate::leanh::LeanObject,
    mut v___y_5844_: *mut crate::leanh::LeanObject,
    mut v___y_5845_: *mut crate::leanh::LeanObject,
    mut v___y_5846_: *mut crate::leanh::LeanObject,
    mut v___y_5847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_5848_: u8 = 0;
    let mut v_skipConstInApp_boxed_5849_: u8 = 0;
    let mut v_skipInstances_boxed_5850_: u8 = 0;
    let mut v_res_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_5848_ = (crate::leanh::lean_unbox(v_usedLetOnly_5837_) as u8);
    v_skipConstInApp_boxed_5849_ = (crate::leanh::lean_unbox(v_skipConstInApp_5838_) as u8);
    v_skipInstances_boxed_5850_ = (crate::leanh::lean_unbox(v_skipInstances_5839_) as u8);
    v_res_5851_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v_upperBound_5833_, v___x_5834_, v_pre_5835_, v_post_5836_, v_usedLetOnly_boxed_5848_, v_skipConstInApp_boxed_5849_, v_skipInstances_boxed_5850_, v_a_5840_, v_b_5841_, v___y_5842_, v___y_5843_, v___y_5844_, v___y_5845_, v___y_5846_);
    crate::leanh::lean_dec(v___y_5846_);
    crate::leanh::lean_dec_ref(v___y_5845_);
    crate::leanh::lean_dec(v___y_5844_);
    crate::leanh::lean_dec_ref(v___y_5843_);
    crate::leanh::lean_dec(v___y_5842_);
    crate::leanh::lean_dec_ref(v___x_5834_);
    crate::leanh::lean_dec(v_upperBound_5833_);
    return v_res_5851_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8___boxed(
    mut v_skipInstances_5852_: *mut crate::leanh::LeanObject,
    mut v_pre_5853_: *mut crate::leanh::LeanObject,
    mut v_post_5854_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5855_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_5856_: *mut crate::leanh::LeanObject,
    mut v_x_5857_: *mut crate::leanh::LeanObject,
    mut v_x_5858_: *mut crate::leanh::LeanObject,
    mut v_x_5859_: *mut crate::leanh::LeanObject,
    mut v___y_5860_: *mut crate::leanh::LeanObject,
    mut v___y_5861_: *mut crate::leanh::LeanObject,
    mut v___y_5862_: *mut crate::leanh::LeanObject,
    mut v___y_5863_: *mut crate::leanh::LeanObject,
    mut v___y_5864_: *mut crate::leanh::LeanObject,
    mut v___y_5865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipInstances_boxed_5866_: u8 = 0;
    let mut v_usedLetOnly_boxed_5867_: u8 = 0;
    let mut v_skipConstInApp_boxed_5868_: u8 = 0;
    let mut v_res_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipInstances_boxed_5866_ = (crate::leanh::lean_unbox(v_skipInstances_5852_) as u8);
    v_usedLetOnly_boxed_5867_ = (crate::leanh::lean_unbox(v_usedLetOnly_5855_) as u8);
    v_skipConstInApp_boxed_5868_ = (crate::leanh::lean_unbox(v_skipConstInApp_5856_) as u8);
    v_res_5869_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(v_skipInstances_boxed_5866_, v_pre_5853_, v_post_5854_, v_usedLetOnly_boxed_5867_, v_skipConstInApp_boxed_5868_, v_x_5857_, v_x_5858_, v_x_5859_, v___y_5860_, v___y_5861_, v___y_5862_, v___y_5863_, v___y_5864_);
    crate::leanh::lean_dec(v___y_5864_);
    crate::leanh::lean_dec_ref(v___y_5863_);
    crate::leanh::lean_dec(v___y_5862_);
    crate::leanh::lean_dec_ref(v___y_5861_);
    crate::leanh::lean_dec(v___y_5860_);
    return v_res_5869_;
}
pub unsafe fn _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5870_ = crate::leanh::lean_box(0);
    v___x_5871_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_5872_ = lean_mk_array(v___x_5871_, v___x_5870_);
    return v___x_5872_;
}
pub unsafe fn _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5873_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0_once
        ),
        _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0,
    );
    v___x_5874_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5875_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5875_, 0, v___x_5874_);
    crate::leanh::lean_ctor_set(v___x_5875_, 1, v___x_5873_);
    return v___x_5875_;
}
pub unsafe fn _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5876_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once
        ),
        _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1,
    );
    v___x_5877_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_5877_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5877_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5877_, 2, v___x_5876_);
    return v___x_5877_;
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(
    mut v_input_5878_: *mut crate::leanh::LeanObject,
    mut v_pre_5879_: *mut crate::leanh::LeanObject,
    mut v_post_5880_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5881_: u8,
    mut v_skipConstInApp_5882_: u8,
    mut v___y_5883_: *mut crate::leanh::LeanObject,
    mut v___y_5884_: *mut crate::leanh::LeanObject,
    mut v___y_5885_: *mut crate::leanh::LeanObject,
    mut v___y_5886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: u8 = 0;
    let mut v___x_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5898_: u8 = 0;
    let mut v___x_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5902_: u8 = 0;
    let mut v_unused_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5888_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once), _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
                v___x_5889_ =
                    l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(
                        crate::leanh::lean_box(0),
                        v___x_5888_,
                        v___y_5883_,
                        v___y_5884_,
                        v___y_5885_,
                        v___y_5886_,
                    );
                v_a_5890_ = crate::leanh::lean_ctor_get(v___x_5889_, 0);
                crate::leanh::lean_inc(v_a_5890_);
                crate::leanh::lean_dec_ref(v___x_5889_);
                v___x_5891_ = 0;
                v___x_5892_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_5879_, v_post_5880_, v_usedLetOnly_5881_, v_skipConstInApp_5882_, v___x_5891_, v_input_5878_, v_a_5890_, v___y_5883_, v___y_5884_, v___y_5885_, v___y_5886_);
                if crate::leanh::lean_obj_tag(v___x_5892_) == 0 {
                    v_a_5893_ = crate::leanh::lean_ctor_get(v___x_5892_, 0);
                    crate::leanh::lean_inc(v_a_5893_);
                    crate::leanh::lean_dec_ref_known(v___x_5892_, 1);
                    v___x_5894_ = crate::leanh::lean_alloc_closure(
                        l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___x_5894_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_5894_, 1, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_5894_, 2, v_a_5890_);
                    v___x_5895_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(crate::leanh::lean_box(0), v___x_5894_, v___y_5883_, v___y_5884_, v___y_5885_, v___y_5886_);
                    v_isSharedCheck_5902_ = (!crate::leanh::lean_is_exclusive(v___x_5895_)) as u8;
                    if v_isSharedCheck_5902_ == 0 {
                        v_unused_5903_ = crate::leanh::lean_ctor_get(v___x_5895_, 0);
                        crate::leanh::lean_dec(v_unused_5903_);
                        v___x_5897_ = v___x_5895_;
                        v_isShared_5898_ = v_isSharedCheck_5902_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5895_);
                        v___x_5897_ = crate::leanh::lean_box(0);
                        v_isShared_5898_ = v_isSharedCheck_5902_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5890_);
                    return v___x_5892_;
                }
            }
            1 => {
                if v_isShared_5898_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5897_, 0, v_a_5893_);
                    v___x_5900_ = v___x_5897_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5901_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5901_, 0, v_a_5893_);
                    v___x_5900_ = v_reuseFailAlloc_5901_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5900_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___boxed(
    mut v_input_5904_: *mut crate::leanh::LeanObject,
    mut v_pre_5905_: *mut crate::leanh::LeanObject,
    mut v_post_5906_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5907_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_5908_: *mut crate::leanh::LeanObject,
    mut v___y_5909_: *mut crate::leanh::LeanObject,
    mut v___y_5910_: *mut crate::leanh::LeanObject,
    mut v___y_5911_: *mut crate::leanh::LeanObject,
    mut v___y_5912_: *mut crate::leanh::LeanObject,
    mut v___y_5913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_5914_: u8 = 0;
    let mut v_skipConstInApp_boxed_5915_: u8 = 0;
    let mut v_res_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_5914_ = (crate::leanh::lean_unbox(v_usedLetOnly_5907_) as u8);
    v_skipConstInApp_boxed_5915_ = (crate::leanh::lean_unbox(v_skipConstInApp_5908_) as u8);
    v_res_5916_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(
        v_input_5904_,
        v_pre_5905_,
        v_post_5906_,
        v_usedLetOnly_boxed_5914_,
        v_skipConstInApp_boxed_5915_,
        v___y_5909_,
        v___y_5910_,
        v___y_5911_,
        v___y_5912_,
    );
    crate::leanh::lean_dec(v___y_5912_);
    crate::leanh::lean_dec_ref(v___y_5911_);
    crate::leanh::lean_dec(v___y_5910_);
    crate::leanh::lean_dec_ref(v___y_5909_);
    return v_res_5916_;
}
pub unsafe fn l_Lean_Meta_Sym_unfoldReducible(
    mut v_e_5919_: *mut crate::leanh::LeanObject,
    mut v_a_5920_: *mut crate::leanh::LeanObject,
    mut v_a_5921_: *mut crate::leanh::LeanObject,
    mut v_a_5922_: *mut crate::leanh::LeanObject,
    mut v_a_5923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5929_: u8 = 0;
    let mut v___x_5930_: u8 = 0;
    let mut v___x_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: u8 = 0;
    let mut v___x_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5938_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5925_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_5919_, v_a_5923_);
                v_a_5926_ = crate::leanh::lean_ctor_get(v___x_5925_, 0);
                v_isSharedCheck_5938_ = (!crate::leanh::lean_is_exclusive(v___x_5925_)) as u8;
                if v_isSharedCheck_5938_ == 0 {
                    v___x_5928_ = v___x_5925_;
                    v_isShared_5929_ = v_isSharedCheck_5938_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5926_);
                    crate::leanh::lean_dec(v___x_5925_);
                    v___x_5928_ = crate::leanh::lean_box(0);
                    v_isShared_5929_ = v_isSharedCheck_5938_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5930_ = (crate::leanh::lean_unbox(v_a_5926_) as u8);
                crate::leanh::lean_dec(v_a_5926_);
                if v___x_5930_ == 0 {
                    if v_isShared_5929_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5928_, 0, v_e_5919_);
                        v___x_5932_ = v___x_5928_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5933_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5933_, 0, v_e_5919_);
                        v___x_5932_ = v_reuseFailAlloc_5933_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5928_);
                    v___f_5934_ = l_Lean_Meta_Sym_unfoldReducible___closed__0;
                    v___x_5935_ = 0;
                    v___x_5936_ = l_Lean_Meta_Sym_unfoldReducible___closed__1;
                    v___x_5937_ =
                        l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(
                            v_e_5919_,
                            v___x_5936_,
                            v___f_5934_,
                            v___x_5935_,
                            v___x_5935_,
                            v_a_5920_,
                            v_a_5921_,
                            v_a_5922_,
                            v_a_5923_,
                        );
                    return v___x_5937_;
                }
            }
            2 => {
                return v___x_5932_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_unfoldReducible___boxed(
    mut v_e_5939_: *mut crate::leanh::LeanObject,
    mut v_a_5940_: *mut crate::leanh::LeanObject,
    mut v_a_5941_: *mut crate::leanh::LeanObject,
    mut v_a_5942_: *mut crate::leanh::LeanObject,
    mut v_a_5943_: *mut crate::leanh::LeanObject,
    mut v_a_5944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5945_ =
        l_Lean_Meta_Sym_unfoldReducible(v_e_5939_, v_a_5940_, v_a_5941_, v_a_5942_, v_a_5943_);
    crate::leanh::lean_dec(v_a_5943_);
    crate::leanh::lean_dec_ref(v_a_5942_);
    crate::leanh::lean_dec(v_a_5941_);
    crate::leanh::lean_dec_ref(v_a_5940_);
    return v_res_5945_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(
    mut v_upperBound_5946_: *mut crate::leanh::LeanObject,
    mut v___x_5947_: *mut crate::leanh::LeanObject,
    mut v_pre_5948_: *mut crate::leanh::LeanObject,
    mut v_post_5949_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5950_: u8,
    mut v_skipConstInApp_5951_: u8,
    mut v_skipInstances_5952_: u8,
    mut v___x_5953_: *mut crate::leanh::LeanObject,
    mut v_inst_5954_: *mut crate::leanh::LeanObject,
    mut v_R_5955_: *mut crate::leanh::LeanObject,
    mut v_a_5956_: *mut crate::leanh::LeanObject,
    mut v_b_5957_: *mut crate::leanh::LeanObject,
    mut v_c_5958_: *mut crate::leanh::LeanObject,
    mut v___y_5959_: *mut crate::leanh::LeanObject,
    mut v___y_5960_: *mut crate::leanh::LeanObject,
    mut v___y_5961_: *mut crate::leanh::LeanObject,
    mut v___y_5962_: *mut crate::leanh::LeanObject,
    mut v___y_5963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5965_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v_upperBound_5946_, v___x_5947_, v_pre_5948_, v_post_5949_, v_usedLetOnly_5950_, v_skipConstInApp_5951_, v_skipInstances_5952_, v_a_5956_, v_b_5957_, v___y_5959_, v___y_5960_, v___y_5961_, v___y_5962_, v___y_5963_);
    return v___x_5965_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_upperBound_5966_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_5967_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_pre_5968_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_post_5969_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_usedLetOnly_5970_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_skipConstInApp_5971_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_skipInstances_5972_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_5973_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_inst_5974_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_R_5975_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_a_5976_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_b_5977_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_c_5978_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_5979_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_5980_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_5981_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_5982_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_5983_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_5984_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_usedLetOnly_boxed_5985_: u8 = 0;
    let mut v_skipConstInApp_boxed_5986_: u8 = 0;
    let mut v_skipInstances_boxed_5987_: u8 = 0;
    let mut v_res_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_5985_ = (crate::leanh::lean_unbox(v_usedLetOnly_5970_) as u8);
    v_skipConstInApp_boxed_5986_ = (crate::leanh::lean_unbox(v_skipConstInApp_5971_) as u8);
    v_skipInstances_boxed_5987_ = (crate::leanh::lean_unbox(v_skipInstances_5972_) as u8);
    v_res_5988_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_upperBound_5966_, v___x_5967_, v_pre_5968_, v_post_5969_, v_usedLetOnly_boxed_5985_, v_skipConstInApp_boxed_5986_, v_skipInstances_boxed_5987_, v___x_5973_, v_inst_5974_, v_R_5975_, v_a_5976_, v_b_5977_, v_c_5978_, v___y_5979_, v___y_5980_, v___y_5981_, v___y_5982_, v___y_5983_);
    crate::leanh::lean_dec(v___y_5983_);
    crate::leanh::lean_dec_ref(v___y_5982_);
    crate::leanh::lean_dec(v___y_5981_);
    crate::leanh::lean_dec_ref(v___y_5980_);
    crate::leanh::lean_dec(v___y_5979_);
    crate::leanh::lean_dec(v___x_5973_);
    crate::leanh::lean_dec_ref(v___x_5967_);
    crate::leanh::lean_dec(v_upperBound_5966_);
    return v_res_5988_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(
    mut v_00_u03b2_5989_: *mut crate::leanh::LeanObject,
    mut v_m_5990_: *mut crate::leanh::LeanObject,
    mut v_a_5991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5992_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_m_5990_, v_a_5991_);
    return v___x_5992_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___boxed(
    mut v_00_u03b2_5993_: *mut crate::leanh::LeanObject,
    mut v_m_5994_: *mut crate::leanh::LeanObject,
    mut v_a_5995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5996_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(v_00_u03b2_5993_, v_m_5994_, v_a_5995_);
    crate::leanh::lean_dec_ref(v_a_5995_);
    crate::leanh::lean_dec_ref(v_m_5994_);
    return v_res_5996_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(
    mut v_00_u03b1_5997_: *mut crate::leanh::LeanObject,
    mut v_name_5998_: *mut crate::leanh::LeanObject,
    mut v_bi_5999_: u8,
    mut v_type_6000_: *mut crate::leanh::LeanObject,
    mut v_k_6001_: *mut crate::leanh::LeanObject,
    mut v_kind_6002_: u8,
    mut v___y_6003_: *mut crate::leanh::LeanObject,
    mut v___y_6004_: *mut crate::leanh::LeanObject,
    mut v___y_6005_: *mut crate::leanh::LeanObject,
    mut v___y_6006_: *mut crate::leanh::LeanObject,
    mut v___y_6007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6009_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_name_5998_, v_bi_5999_, v_type_6000_, v_k_6001_, v_kind_6002_, v___y_6003_, v___y_6004_, v___y_6005_, v___y_6006_, v___y_6007_);
    return v___x_6009_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___boxed(
    mut v_00_u03b1_6010_: *mut crate::leanh::LeanObject,
    mut v_name_6011_: *mut crate::leanh::LeanObject,
    mut v_bi_6012_: *mut crate::leanh::LeanObject,
    mut v_type_6013_: *mut crate::leanh::LeanObject,
    mut v_k_6014_: *mut crate::leanh::LeanObject,
    mut v_kind_6015_: *mut crate::leanh::LeanObject,
    mut v___y_6016_: *mut crate::leanh::LeanObject,
    mut v___y_6017_: *mut crate::leanh::LeanObject,
    mut v___y_6018_: *mut crate::leanh::LeanObject,
    mut v___y_6019_: *mut crate::leanh::LeanObject,
    mut v___y_6020_: *mut crate::leanh::LeanObject,
    mut v___y_6021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_6022_: u8 = 0;
    let mut v_kind_boxed_6023_: u8 = 0;
    let mut v_res_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_6022_ = (crate::leanh::lean_unbox(v_bi_6012_) as u8);
    v_kind_boxed_6023_ = (crate::leanh::lean_unbox(v_kind_6015_) as u8);
    v_res_6024_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_6010_, v_name_6011_, v_bi_boxed_6022_, v_type_6013_, v_k_6014_, v_kind_boxed_6023_, v___y_6016_, v___y_6017_, v___y_6018_, v___y_6019_, v___y_6020_);
    crate::leanh::lean_dec(v___y_6020_);
    crate::leanh::lean_dec_ref(v___y_6019_);
    crate::leanh::lean_dec(v___y_6018_);
    crate::leanh::lean_dec_ref(v___y_6017_);
    crate::leanh::lean_dec(v___y_6016_);
    return v_res_6024_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(
    mut v_00_u03b1_6025_: *mut crate::leanh::LeanObject,
    mut v_name_6026_: *mut crate::leanh::LeanObject,
    mut v_type_6027_: *mut crate::leanh::LeanObject,
    mut v_val_6028_: *mut crate::leanh::LeanObject,
    mut v_k_6029_: *mut crate::leanh::LeanObject,
    mut v_nondep_6030_: u8,
    mut v_kind_6031_: u8,
    mut v___y_6032_: *mut crate::leanh::LeanObject,
    mut v___y_6033_: *mut crate::leanh::LeanObject,
    mut v___y_6034_: *mut crate::leanh::LeanObject,
    mut v___y_6035_: *mut crate::leanh::LeanObject,
    mut v___y_6036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6038_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_name_6026_, v_type_6027_, v_val_6028_, v_k_6029_, v_nondep_6030_, v_kind_6031_, v___y_6032_, v___y_6033_, v___y_6034_, v___y_6035_, v___y_6036_);
    return v___x_6038_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___boxed(
    mut v_00_u03b1_6039_: *mut crate::leanh::LeanObject,
    mut v_name_6040_: *mut crate::leanh::LeanObject,
    mut v_type_6041_: *mut crate::leanh::LeanObject,
    mut v_val_6042_: *mut crate::leanh::LeanObject,
    mut v_k_6043_: *mut crate::leanh::LeanObject,
    mut v_nondep_6044_: *mut crate::leanh::LeanObject,
    mut v_kind_6045_: *mut crate::leanh::LeanObject,
    mut v___y_6046_: *mut crate::leanh::LeanObject,
    mut v___y_6047_: *mut crate::leanh::LeanObject,
    mut v___y_6048_: *mut crate::leanh::LeanObject,
    mut v___y_6049_: *mut crate::leanh::LeanObject,
    mut v___y_6050_: *mut crate::leanh::LeanObject,
    mut v___y_6051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nondep_boxed_6052_: u8 = 0;
    let mut v_kind_boxed_6053_: u8 = 0;
    let mut v_res_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_6052_ = (crate::leanh::lean_unbox(v_nondep_6044_) as u8);
    v_kind_boxed_6053_ = (crate::leanh::lean_unbox(v_kind_6045_) as u8);
    v_res_6054_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_6039_, v_name_6040_, v_type_6041_, v_val_6042_, v_k_6043_, v_nondep_boxed_6052_, v_kind_boxed_6053_, v___y_6046_, v___y_6047_, v___y_6048_, v___y_6049_, v___y_6050_);
    crate::leanh::lean_dec(v___y_6050_);
    crate::leanh::lean_dec_ref(v___y_6049_);
    crate::leanh::lean_dec(v___y_6048_);
    crate::leanh::lean_dec_ref(v___y_6047_);
    crate::leanh::lean_dec(v___y_6046_);
    return v_res_6054_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(
    mut v_00_u03b1_6055_: *mut crate::leanh::LeanObject,
    mut v_ref_6056_: *mut crate::leanh::LeanObject,
    mut v___y_6057_: *mut crate::leanh::LeanObject,
    mut v___y_6058_: *mut crate::leanh::LeanObject,
    mut v___y_6059_: *mut crate::leanh::LeanObject,
    mut v___y_6060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6062_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_6056_);
    return v___x_6062_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___boxed(
    mut v_00_u03b1_6063_: *mut crate::leanh::LeanObject,
    mut v_ref_6064_: *mut crate::leanh::LeanObject,
    mut v___y_6065_: *mut crate::leanh::LeanObject,
    mut v___y_6066_: *mut crate::leanh::LeanObject,
    mut v___y_6067_: *mut crate::leanh::LeanObject,
    mut v___y_6068_: *mut crate::leanh::LeanObject,
    mut v___y_6069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6070_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_6063_, v_ref_6064_, v___y_6065_, v___y_6066_, v___y_6067_, v___y_6068_);
    crate::leanh::lean_dec(v___y_6068_);
    crate::leanh::lean_dec_ref(v___y_6067_);
    crate::leanh::lean_dec(v___y_6066_);
    crate::leanh::lean_dec_ref(v___y_6065_);
    return v_res_6070_;
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(
    mut v_00_u03b1_6071_: *mut crate::leanh::LeanObject,
    mut v_x_6072_: *mut crate::leanh::LeanObject,
    mut v___y_6073_: *mut crate::leanh::LeanObject,
    mut v___y_6074_: *mut crate::leanh::LeanObject,
    mut v___y_6075_: *mut crate::leanh::LeanObject,
    mut v___y_6076_: *mut crate::leanh::LeanObject,
    mut v___y_6077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6079_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v_x_6072_, v___y_6073_, v___y_6074_, v___y_6075_, v___y_6076_, v___y_6077_);
    return v___x_6079_;
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___boxed(
    mut v_00_u03b1_6080_: *mut crate::leanh::LeanObject,
    mut v_x_6081_: *mut crate::leanh::LeanObject,
    mut v___y_6082_: *mut crate::leanh::LeanObject,
    mut v___y_6083_: *mut crate::leanh::LeanObject,
    mut v___y_6084_: *mut crate::leanh::LeanObject,
    mut v___y_6085_: *mut crate::leanh::LeanObject,
    mut v___y_6086_: *mut crate::leanh::LeanObject,
    mut v___y_6087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6088_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(v_00_u03b1_6080_, v_x_6081_, v___y_6082_, v___y_6083_, v___y_6084_, v___y_6085_, v___y_6086_);
    crate::leanh::lean_dec(v___y_6086_);
    crate::leanh::lean_dec_ref(v___y_6085_);
    crate::leanh::lean_dec(v___y_6084_);
    crate::leanh::lean_dec_ref(v___y_6083_);
    crate::leanh::lean_dec(v___y_6082_);
    return v_res_6088_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10(
    mut v_00_u03b2_6089_: *mut crate::leanh::LeanObject,
    mut v_m_6090_: *mut crate::leanh::LeanObject,
    mut v_a_6091_: *mut crate::leanh::LeanObject,
    mut v_b_6092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6093_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v_m_6090_, v_a_6091_, v_b_6092_);
    return v___x_6093_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5(
    mut v_00_u03b2_6094_: *mut crate::leanh::LeanObject,
    mut v_a_6095_: *mut crate::leanh::LeanObject,
    mut v_x_6096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6097_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_6095_, v_x_6096_);
    return v___x_6097_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___boxed(
    mut v_00_u03b2_6098_: *mut crate::leanh::LeanObject,
    mut v_a_6099_: *mut crate::leanh::LeanObject,
    mut v_x_6100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6101_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5(v_00_u03b2_6098_, v_a_6099_, v_x_6100_);
    crate::leanh::lean_dec(v_x_6100_);
    crate::leanh::lean_dec_ref(v_a_6099_);
    return v_res_6101_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(
    mut v_00_u03b2_6102_: *mut crate::leanh::LeanObject,
    mut v_a_6103_: *mut crate::leanh::LeanObject,
    mut v_x_6104_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6105_: u8 = 0;
    v___x_6105_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_6103_, v_x_6104_);
    return v___x_6105_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___boxed(
    mut v_00_u03b2_6106_: *mut crate::leanh::LeanObject,
    mut v_a_6107_: *mut crate::leanh::LeanObject,
    mut v_x_6108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6109_: u8 = 0;
    let mut v_r_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6109_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_6106_, v_a_6107_, v_x_6108_);
    crate::leanh::lean_dec(v_x_6108_);
    crate::leanh::lean_dec_ref(v_a_6107_);
    v_r_6110_ = crate::leanh::lean_box((v_res_6109_) as usize);
    return v_r_6110_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16(
    mut v_00_u03b2_6111_: *mut crate::leanh::LeanObject,
    mut v_data_6112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6113_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(v_data_6112_);
    return v___x_6113_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17(
    mut v_00_u03b2_6114_: *mut crate::leanh::LeanObject,
    mut v_a_6115_: *mut crate::leanh::LeanObject,
    mut v_b_6116_: *mut crate::leanh::LeanObject,
    mut v_x_6117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6118_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_6115_, v_b_6116_, v_x_6117_);
    return v___x_6118_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17(
    mut v_00_u03b2_6119_: *mut crate::leanh::LeanObject,
    mut v_i_6120_: *mut crate::leanh::LeanObject,
    mut v_source_6121_: *mut crate::leanh::LeanObject,
    mut v_target_6122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6123_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v_i_6120_, v_source_6121_, v_target_6122_);
    return v___x_6123_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(
    mut v_00_u03b2_6124_: *mut crate::leanh::LeanObject,
    mut v_x_6125_: *mut crate::leanh::LeanObject,
    mut v_x_6126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6127_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_x_6125_, v_x_6126_);
    return v___x_6127_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(
    mut v_msgData_6128_: *mut crate::leanh::LeanObject,
    mut v___y_6129_: *mut crate::leanh::LeanObject,
    mut v___y_6130_: *mut crate::leanh::LeanObject,
    mut v___y_6131_: *mut crate::leanh::LeanObject,
    mut v___y_6132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_6138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6134_ = lean_st_ref_get(v___y_6132_);
    v_env_6135_ = crate::leanh::lean_ctor_get(v___x_6134_, 0);
    crate::leanh::lean_inc_ref(v_env_6135_);
    crate::leanh::lean_dec(v___x_6134_);
    v___x_6136_ = lean_st_ref_get(v___y_6130_);
    v_mctx_6137_ = crate::leanh::lean_ctor_get(v___x_6136_, 0);
    crate::leanh::lean_inc_ref(v_mctx_6137_);
    crate::leanh::lean_dec(v___x_6136_);
    v_lctx_6138_ = crate::leanh::lean_ctor_get(v___y_6129_, 2);
    v_options_6139_ = crate::leanh::lean_ctor_get(v___y_6131_, 2);
    crate::leanh::lean_inc_ref(v_options_6139_);
    crate::leanh::lean_inc_ref(v_lctx_6138_);
    v___x_6140_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6140_, 0, v_env_6135_);
    crate::leanh::lean_ctor_set(v___x_6140_, 1, v_mctx_6137_);
    crate::leanh::lean_ctor_set(v___x_6140_, 2, v_lctx_6138_);
    crate::leanh::lean_ctor_set(v___x_6140_, 3, v_options_6139_);
    v___x_6141_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6141_, 0, v___x_6140_);
    crate::leanh::lean_ctor_set(v___x_6141_, 1, v_msgData_6128_);
    v___x_6142_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6142_, 0, v___x_6141_);
    return v___x_6142_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0___boxed(
    mut v_msgData_6143_: *mut crate::leanh::LeanObject,
    mut v___y_6144_: *mut crate::leanh::LeanObject,
    mut v___y_6145_: *mut crate::leanh::LeanObject,
    mut v___y_6146_: *mut crate::leanh::LeanObject,
    mut v___y_6147_: *mut crate::leanh::LeanObject,
    mut v___y_6148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6149_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msgData_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_);
    crate::leanh::lean_dec(v___y_6147_);
    crate::leanh::lean_dec_ref(v___y_6146_);
    crate::leanh::lean_dec(v___y_6145_);
    crate::leanh::lean_dec_ref(v___y_6144_);
    return v_res_6149_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0() -> f64 {
    let mut v___x_6150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6151_: f64 = 0.0;
    v___x_6150_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6151_ = lean_float_of_nat(v___x_6150_);
    return v___x_6151_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(
    mut v_cls_6155_: *mut crate::leanh::LeanObject,
    mut v_msg_6156_: *mut crate::leanh::LeanObject,
    mut v___y_6157_: *mut crate::leanh::LeanObject,
    mut v___y_6158_: *mut crate::leanh::LeanObject,
    mut v___y_6159_: *mut crate::leanh::LeanObject,
    mut v___y_6160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6167_: u8 = 0;
    let mut v___x_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6180_: u8 = 0;
    let mut v_tid_6181_: u64 = 0;
    let mut v_traces_6182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6185_: u8 = 0;
    let mut v___x_6186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6187_: f64 = 0.0;
    let mut v___x_6188_: u8 = 0;
    let mut v___x_6189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6206_: u8 = 0;
    let mut v_isSharedCheck_6207_: u8 = 0;
    let mut v_isSharedCheck_6208_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_6162_ = crate::leanh::lean_ctor_get(v___y_6159_, 5);
                v___x_6163_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_6156_, v___y_6157_, v___y_6158_, v___y_6159_, v___y_6160_);
                v_a_6164_ = crate::leanh::lean_ctor_get(v___x_6163_, 0);
                v_isSharedCheck_6208_ = (!crate::leanh::lean_is_exclusive(v___x_6163_)) as u8;
                if v_isSharedCheck_6208_ == 0 {
                    v___x_6166_ = v___x_6163_;
                    v_isShared_6167_ = v_isSharedCheck_6208_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6164_);
                    crate::leanh::lean_dec(v___x_6163_);
                    v___x_6166_ = crate::leanh::lean_box(0);
                    v_isShared_6167_ = v_isSharedCheck_6208_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6168_ = lean_st_ref_take(v___y_6160_);
                v_traceState_6169_ = crate::leanh::lean_ctor_get(v___x_6168_, 4);
                v_env_6170_ = crate::leanh::lean_ctor_get(v___x_6168_, 0);
                v_nextMacroScope_6171_ = crate::leanh::lean_ctor_get(v___x_6168_, 1);
                v_ngen_6172_ = crate::leanh::lean_ctor_get(v___x_6168_, 2);
                v_auxDeclNGen_6173_ = crate::leanh::lean_ctor_get(v___x_6168_, 3);
                v_cache_6174_ = crate::leanh::lean_ctor_get(v___x_6168_, 5);
                v_messages_6175_ = crate::leanh::lean_ctor_get(v___x_6168_, 6);
                v_infoState_6176_ = crate::leanh::lean_ctor_get(v___x_6168_, 7);
                v_snapshotTasks_6177_ = crate::leanh::lean_ctor_get(v___x_6168_, 8);
                v_isSharedCheck_6207_ = (!crate::leanh::lean_is_exclusive(v___x_6168_)) as u8;
                if v_isSharedCheck_6207_ == 0 {
                    v___x_6179_ = v___x_6168_;
                    v_isShared_6180_ = v_isSharedCheck_6207_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_6177_);
                    crate::leanh::lean_inc(v_infoState_6176_);
                    crate::leanh::lean_inc(v_messages_6175_);
                    crate::leanh::lean_inc(v_cache_6174_);
                    crate::leanh::lean_inc(v_traceState_6169_);
                    crate::leanh::lean_inc(v_auxDeclNGen_6173_);
                    crate::leanh::lean_inc(v_ngen_6172_);
                    crate::leanh::lean_inc(v_nextMacroScope_6171_);
                    crate::leanh::lean_inc(v_env_6170_);
                    crate::leanh::lean_dec(v___x_6168_);
                    v___x_6179_ = crate::leanh::lean_box(0);
                    v_isShared_6180_ = v_isSharedCheck_6207_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_6181_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_6169_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_6182_ = crate::leanh::lean_ctor_get(v_traceState_6169_, 0);
                v_isSharedCheck_6206_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_6169_)) as u8;
                if v_isSharedCheck_6206_ == 0 {
                    v___x_6184_ = v_traceState_6169_;
                    v_isShared_6185_ = v_isSharedCheck_6206_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_6182_);
                    crate::leanh::lean_dec(v_traceState_6169_);
                    v___x_6184_ = crate::leanh::lean_box(0);
                    v_isShared_6185_ = v_isSharedCheck_6206_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6186_ = crate::leanh::lean_box(0);
                v___x_6187_ = crate::leanh::lean_float_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once
                    ),
                    _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0,
                );
                v___x_6188_ = 0;
                v___x_6189_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1;
                v___x_6190_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_6190_, 0, v_cls_6155_);
                crate::leanh::lean_ctor_set(v___x_6190_, 1, v___x_6186_);
                crate::leanh::lean_ctor_set(v___x_6190_, 2, v___x_6189_);
                crate::leanh::lean_ctor_set_float(
                    v___x_6190_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_6187_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_6190_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_6187_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6190_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_6188_,
                );
                v___x_6191_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2;
                v___x_6192_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6192_, 0, v___x_6190_);
                crate::leanh::lean_ctor_set(v___x_6192_, 1, v_a_6164_);
                crate::leanh::lean_ctor_set(v___x_6192_, 2, v___x_6191_);
                crate::leanh::lean_inc(v_ref_6162_);
                v___x_6193_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6193_, 0, v_ref_6162_);
                crate::leanh::lean_ctor_set(v___x_6193_, 1, v___x_6192_);
                v___x_6194_ = l_Lean_PersistentArray_push___redArg(v_traces_6182_, v___x_6193_);
                if v_isShared_6185_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6184_, 0, v___x_6194_);
                    v___x_6196_ = v___x_6184_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6205_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6205_, 0, v___x_6194_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_6205_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_6181_,
                    );
                    v___x_6196_ = v_reuseFailAlloc_6205_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6180_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6179_, 4, v___x_6196_);
                    v___x_6198_ = v___x_6179_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6204_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6204_, 0, v_env_6170_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6204_, 1, v_nextMacroScope_6171_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6204_, 2, v_ngen_6172_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6204_, 3, v_auxDeclNGen_6173_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6204_, 4, v___x_6196_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6204_, 5, v_cache_6174_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6204_, 6, v_messages_6175_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6204_, 7, v_infoState_6176_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6204_, 8, v_snapshotTasks_6177_);
                    v___x_6198_ = v_reuseFailAlloc_6204_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6199_ = lean_st_ref_set(v___y_6160_, v___x_6198_);
                v___x_6200_ = crate::leanh::lean_box(0);
                if v_isShared_6167_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6166_, 0, v___x_6200_);
                    v___x_6202_ = v___x_6166_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6203_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6203_, 0, v___x_6200_);
                    v___x_6202_ = v_reuseFailAlloc_6203_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6202_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___boxed(
    mut v_cls_6209_: *mut crate::leanh::LeanObject,
    mut v_msg_6210_: *mut crate::leanh::LeanObject,
    mut v___y_6211_: *mut crate::leanh::LeanObject,
    mut v___y_6212_: *mut crate::leanh::LeanObject,
    mut v___y_6213_: *mut crate::leanh::LeanObject,
    mut v___y_6214_: *mut crate::leanh::LeanObject,
    mut v___y_6215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6216_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(
        v_cls_6209_,
        v_msg_6210_,
        v___y_6211_,
        v___y_6212_,
        v___y_6213_,
        v___y_6214_,
    );
    crate::leanh::lean_dec(v___y_6214_);
    crate::leanh::lean_dec_ref(v___y_6213_);
    crate::leanh::lean_dec(v___y_6212_);
    crate::leanh::lean_dec_ref(v___y_6211_);
    return v_res_6216_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_6225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6225_ = l_Lean_Meta_Sym_foldProjs___lam__0___closed__2;
    v___x_6226_ = l_Lean_Meta_Sym_foldProjs___lam__0___closed__4;
    v___x_6227_ = l_Lean_Name_append(v___x_6226_, v___x_6225_);
    return v___x_6227_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__7() -> *mut crate::leanh::LeanObject
{
    let mut v___x_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6229_ = l_Lean_Meta_Sym_foldProjs___lam__0___closed__6;
    v___x_6230_ = l_Lean_stringToMessageData(v___x_6229_);
    return v___x_6230_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__9() -> *mut crate::leanh::LeanObject
{
    let mut v___x_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6232_ = l_Lean_Meta_Sym_foldProjs___lam__0___closed__8;
    v___x_6233_ = l_Lean_stringToMessageData(v___x_6232_);
    return v___x_6233_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__10() -> u64 {
    let mut v___x_6234_: u8 = 0;
    let mut v___x_6235_: u64 = 0;
    v___x_6234_ = 1;
    v___x_6235_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_6234_);
    return v___x_6235_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6237_ = l_Lean_Meta_Sym_foldProjs___lam__0___closed__11;
    v___x_6238_ = l_Lean_stringToMessageData(v___x_6237_);
    return v___x_6238_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6240_ = l_Lean_Meta_Sym_foldProjs___lam__0___closed__13;
    v___x_6241_ = l_Lean_stringToMessageData(v___x_6240_);
    return v___x_6241_;
}
pub unsafe fn l_Lean_Meta_Sym_foldProjs___lam__0(
    mut v_e_6242_: *mut crate::leanh::LeanObject,
    mut v___y_6243_: *mut crate::leanh::LeanObject,
    mut v___y_6244_: *mut crate::leanh::LeanObject,
    mut v___y_6245_: *mut crate::leanh::LeanObject,
    mut v___y_6246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_6254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_6256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6263_: u8 = 0;
    let mut v_fieldNames_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6266_: u8 = 0;
    let mut v_options_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6268_: u8 = 0;
    let mut v_inheritedTraceOptions_6269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: u8 = 0;
    let mut v___x_6273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6287_: u8 = 0;
    let mut v___x_6289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6291_: u8 = 0;
    let mut v_reuseFailAlloc_6292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_6294_: u8 = 0;
    let mut v_ctxApprox_6295_: u8 = 0;
    let mut v_quasiPatternApprox_6296_: u8 = 0;
    let mut v_constApprox_6297_: u8 = 0;
    let mut v_isDefEqStuckEx_6298_: u8 = 0;
    let mut v_unificationHints_6299_: u8 = 0;
    let mut v_proofIrrelevance_6300_: u8 = 0;
    let mut v_assignSyntheticOpaque_6301_: u8 = 0;
    let mut v_offsetCnstrs_6302_: u8 = 0;
    let mut v_etaStruct_6303_: u8 = 0;
    let mut v_univApprox_6304_: u8 = 0;
    let mut v_iota_6305_: u8 = 0;
    let mut v_beta_6306_: u8 = 0;
    let mut v_proj_6307_: u8 = 0;
    let mut v_zeta_6308_: u8 = 0;
    let mut v_zetaDelta_6309_: u8 = 0;
    let mut v_zetaUnused_6310_: u8 = 0;
    let mut v_zetaHave_6311_: u8 = 0;
    let mut v___x_6313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6314_: u8 = 0;
    let mut v_trackZetaDelta_6315_: u8 = 0;
    let mut v_zetaDeltaSet_6316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_6317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_6318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_6319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_6320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_6321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_6322_: u8 = 0;
    let mut v_inTypeClassResolution_6323_: u8 = 0;
    let mut v_cacheInferType_6324_: u8 = 0;
    let mut v___x_6325_: u8 = 0;
    let mut v_config_6327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: u64 = 0;
    let mut v___x_6329_: u64 = 0;
    let mut v___x_6330_: u64 = 0;
    let mut v___x_6331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: u64 = 0;
    let mut v___x_6333_: u64 = 0;
    let mut v_key_6334_: u64 = 0;
    let mut v___x_6335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6341_: u8 = 0;
    let mut v___x_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6348_: u8 = 0;
    let mut v_a_6349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6352_: u8 = 0;
    let mut v___x_6354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6356_: u8 = 0;
    let mut v_reuseFailAlloc_6357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6358_: u8 = 0;
    let mut v_isSharedCheck_6359_: u8 = 0;
    let mut v_options_6360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6361_: u8 = 0;
    let mut v_inheritedTraceOptions_6362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6365_: u8 = 0;
    let mut v___x_6366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6377_: u8 = 0;
    let mut v___x_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6381_: u8 = 0;
    let mut v___x_6382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_6242_) == 11 {
                    v_typeName_6254_ = crate::leanh::lean_ctor_get(v_e_6242_, 0);
                    v_idx_6255_ = crate::leanh::lean_ctor_get(v_e_6242_, 1);
                    v_struct_6256_ = crate::leanh::lean_ctor_get(v_e_6242_, 2);
                    v___x_6257_ = lean_st_ref_get(v___y_6246_);
                    v_env_6258_ = crate::leanh::lean_ctor_get(v___x_6257_, 0);
                    crate::leanh::lean_inc_ref(v_env_6258_);
                    crate::leanh::lean_dec(v___x_6257_);
                    crate::leanh::lean_inc(v_typeName_6254_);
                    v___x_6259_ = l_Lean_getStructureInfo_x3f(v_env_6258_, v_typeName_6254_);
                    if crate::leanh::lean_obj_tag(v___x_6259_) == 1 {
                        v_val_6260_ = crate::leanh::lean_ctor_get(v___x_6259_, 0);
                        v_isSharedCheck_6359_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6259_)) as u8;
                        if v_isSharedCheck_6359_ == 0 {
                            v___x_6262_ = v___x_6259_;
                            v_isShared_6263_ = v_isSharedCheck_6359_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_6260_);
                            crate::leanh::lean_dec(v___x_6259_);
                            v___x_6262_ = crate::leanh::lean_box(0);
                            v_isShared_6263_ = v_isSharedCheck_6359_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_6259_);
                        v_options_6360_ = crate::leanh::lean_ctor_get(v___y_6245_, 2);
                        v_hasTrace_6361_ = crate::leanh::lean_ctor_get_uint8(
                            v_options_6360_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_6361_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v_inheritedTraceOptions_6362_ =
                                crate::leanh::lean_ctor_get(v___y_6245_, 13);
                            v___x_6363_ = l_Lean_Meta_Sym_foldProjs___lam__0___closed__2;
                            v___x_6364_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Sym_foldProjs___lam__0___closed__5
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Sym_foldProjs___lam__0___closed__5_once
                                ),
                                _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__5,
                            );
                            v___x_6365_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_6362_,
                                v_options_6360_,
                                v___x_6364_,
                            );
                            if v___x_6365_ == 0 {
                                state = 2;
                                continue;
                            } else {
                                v___x_6366_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Sym_foldProjs___lam__0___closed__12
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Sym_foldProjs___lam__0___closed__12_once
                                    ),
                                    _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__12,
                                );
                                crate::leanh::lean_inc(v_typeName_6254_);
                                v___x_6367_ = l_Lean_MessageData_ofName(v_typeName_6254_);
                                v___x_6368_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_6368_, 0, v___x_6366_);
                                crate::leanh::lean_ctor_set(v___x_6368_, 1, v___x_6367_);
                                v___x_6369_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Sym_foldProjs___lam__0___closed__14
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Sym_foldProjs___lam__0___closed__14_once
                                    ),
                                    _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__14,
                                );
                                v___x_6370_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_6370_, 0, v___x_6368_);
                                crate::leanh::lean_ctor_set(v___x_6370_, 1, v___x_6369_);
                                crate::leanh::lean_inc_ref(v_e_6242_);
                                v___x_6371_ = l_Lean_indentExpr(v_e_6242_);
                                v___x_6372_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_6372_, 0, v___x_6370_);
                                crate::leanh::lean_ctor_set(v___x_6372_, 1, v___x_6371_);
                                v___x_6373_ =
                                    l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(
                                        v___x_6363_,
                                        v___x_6372_,
                                        v___y_6243_,
                                        v___y_6244_,
                                        v___y_6245_,
                                        v___y_6246_,
                                    );
                                if crate::leanh::lean_obj_tag(v___x_6373_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_6373_, 1);
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref_known(v_e_6242_, 3);
                                    v_a_6374_ = crate::leanh::lean_ctor_get(v___x_6373_, 0);
                                    v_isSharedCheck_6381_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6373_)) as u8;
                                    if v_isSharedCheck_6381_ == 0 {
                                        v___x_6376_ = v___x_6373_;
                                        v_isShared_6377_ = v_isSharedCheck_6381_;
                                        state = 14;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6374_);
                                        crate::leanh::lean_dec(v___x_6373_);
                                        v___x_6376_ = crate::leanh::lean_box(0);
                                        v_isShared_6377_ = v_isSharedCheck_6381_;
                                        state = 14;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    v___x_6382_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6382_, 0, v_e_6242_);
                    v___x_6383_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6383_, 0, v___x_6382_);
                    return v___x_6383_;
                }
            }
            1 => {
                v___x_6249_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6249_, 0, v_e_6242_);
                v___x_6250_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6250_, 0, v___x_6249_);
                return v___x_6250_;
            }
            2 => {
                v___x_6252_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6252_, 0, v_e_6242_);
                v___x_6253_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6253_, 0, v___x_6252_);
                return v___x_6253_;
            }
            3 => {
                v_fieldNames_6264_ = crate::leanh::lean_ctor_get(v_val_6260_, 1);
                crate::leanh::lean_inc_ref(v_fieldNames_6264_);
                crate::leanh::lean_dec(v_val_6260_);
                v___x_6265_ = lean_array_get_size(v_fieldNames_6264_);
                v___x_6266_ = lean_nat_dec_lt(v_idx_6255_, v___x_6265_);
                if v___x_6266_ == 0 {
                    crate::leanh::lean_dec_ref(v_fieldNames_6264_);
                    v_options_6267_ = crate::leanh::lean_ctor_get(v___y_6245_, 2);
                    v_hasTrace_6268_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_6267_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_6268_ == 0 {
                        crate::leanh::lean_del_object(v___x_6262_);
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_6269_ =
                            crate::leanh::lean_ctor_get(v___y_6245_, 13);
                        v___x_6270_ = l_Lean_Meta_Sym_foldProjs___lam__0___closed__2;
                        v___x_6271_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_foldProjs___lam__0___closed__5),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Sym_foldProjs___lam__0___closed__5_once
                            ),
                            _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__5,
                        );
                        v___x_6272_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_6269_,
                            v_options_6267_,
                            v___x_6271_,
                        );
                        if v___x_6272_ == 0 {
                            crate::leanh::lean_del_object(v___x_6262_);
                            state = 1;
                            continue;
                        } else {
                            v___x_6273_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Sym_foldProjs___lam__0___closed__7
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Sym_foldProjs___lam__0___closed__7_once
                                ),
                                _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__7,
                            );
                            crate::leanh::lean_inc(v_idx_6255_);
                            v___x_6274_ = l_Nat_reprFast(v_idx_6255_);
                            if v_isShared_6263_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_6262_, 3);
                                crate::leanh::lean_ctor_set(v___x_6262_, 0, v___x_6274_);
                                v___x_6276_ = v___x_6262_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_6292_ =
                                    crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6292_, 0, v___x_6274_);
                                v___x_6276_ = v_reuseFailAlloc_6292_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_struct_6256_);
                    crate::leanh::lean_inc(v_idx_6255_);
                    crate::leanh::lean_dec_ref_known(v_e_6242_, 3);
                    v___x_6293_ = l_Lean_Meta_Context_config(v___y_6243_);
                    v_foApprox_6294_ = crate::leanh::lean_ctor_get_uint8(v___x_6293_, 0 as u32);
                    v_ctxApprox_6295_ = crate::leanh::lean_ctor_get_uint8(v___x_6293_, 1 as u32);
                    v_quasiPatternApprox_6296_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_6293_, 2 as u32);
                    v_constApprox_6297_ = crate::leanh::lean_ctor_get_uint8(v___x_6293_, 3 as u32);
                    v_isDefEqStuckEx_6298_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_6293_, 4 as u32);
                    v_unificationHints_6299_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_6293_, 5 as u32);
                    v_proofIrrelevance_6300_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_6293_, 6 as u32);
                    v_assignSyntheticOpaque_6301_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_6293_, 7 as u32);
                    v_offsetCnstrs_6302_ = crate::leanh::lean_ctor_get_uint8(v___x_6293_, 8 as u32);
                    v_etaStruct_6303_ = crate::leanh::lean_ctor_get_uint8(v___x_6293_, 10 as u32);
                    v_univApprox_6304_ = crate::leanh::lean_ctor_get_uint8(v___x_6293_, 11 as u32);
                    v_iota_6305_ = crate::leanh::lean_ctor_get_uint8(v___x_6293_, 12 as u32);
                    v_beta_6306_ = crate::leanh::lean_ctor_get_uint8(v___x_6293_, 13 as u32);
                    v_proj_6307_ = crate::leanh::lean_ctor_get_uint8(v___x_6293_, 14 as u32);
                    v_zeta_6308_ = crate::leanh::lean_ctor_get_uint8(v___x_6293_, 15 as u32);
                    v_zetaDelta_6309_ = crate::leanh::lean_ctor_get_uint8(v___x_6293_, 16 as u32);
                    v_zetaUnused_6310_ = crate::leanh::lean_ctor_get_uint8(v___x_6293_, 17 as u32);
                    v_zetaHave_6311_ = crate::leanh::lean_ctor_get_uint8(v___x_6293_, 18 as u32);
                    v_isSharedCheck_6358_ = (!crate::leanh::lean_is_exclusive(v___x_6293_)) as u8;
                    if v_isSharedCheck_6358_ == 0 {
                        v___x_6313_ = v___x_6293_;
                        v_isShared_6314_ = v_isSharedCheck_6358_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6293_);
                        v___x_6313_ = crate::leanh::lean_box(0);
                        v_isShared_6314_ = v_isSharedCheck_6358_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v___x_6277_ = l_Lean_MessageData_ofFormat(v___x_6276_);
                v___x_6278_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6278_, 0, v___x_6273_);
                crate::leanh::lean_ctor_set(v___x_6278_, 1, v___x_6277_);
                v___x_6279_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_foldProjs___lam__0___closed__9),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_foldProjs___lam__0___closed__9_once),
                    _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__9,
                );
                v___x_6280_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6280_, 0, v___x_6278_);
                crate::leanh::lean_ctor_set(v___x_6280_, 1, v___x_6279_);
                crate::leanh::lean_inc_ref(v_e_6242_);
                v___x_6281_ = l_Lean_indentExpr(v_e_6242_);
                v___x_6282_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6282_, 0, v___x_6280_);
                crate::leanh::lean_ctor_set(v___x_6282_, 1, v___x_6281_);
                v___x_6283_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(
                    v___x_6270_,
                    v___x_6282_,
                    v___y_6243_,
                    v___y_6244_,
                    v___y_6245_,
                    v___y_6246_,
                );
                if crate::leanh::lean_obj_tag(v___x_6283_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6283_, 1);
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_e_6242_, 3);
                    v_a_6284_ = crate::leanh::lean_ctor_get(v___x_6283_, 0);
                    v_isSharedCheck_6291_ = (!crate::leanh::lean_is_exclusive(v___x_6283_)) as u8;
                    if v_isSharedCheck_6291_ == 0 {
                        v___x_6286_ = v___x_6283_;
                        v_isShared_6287_ = v_isSharedCheck_6291_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6284_);
                        crate::leanh::lean_dec(v___x_6283_);
                        v___x_6286_ = crate::leanh::lean_box(0);
                        v_isShared_6287_ = v_isSharedCheck_6291_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_6287_ == 0 {
                    v___x_6289_ = v___x_6286_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6290_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6290_, 0, v_a_6284_);
                    v___x_6289_ = v_reuseFailAlloc_6290_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6289_;
            }
            7 => {
                v_trackZetaDelta_6315_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_6243_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_6316_ = crate::leanh::lean_ctor_get(v___y_6243_, 1);
                v_lctx_6317_ = crate::leanh::lean_ctor_get(v___y_6243_, 2);
                v_localInstances_6318_ = crate::leanh::lean_ctor_get(v___y_6243_, 3);
                v_defEqCtx_x3f_6319_ = crate::leanh::lean_ctor_get(v___y_6243_, 4);
                v_synthPendingDepth_6320_ = crate::leanh::lean_ctor_get(v___y_6243_, 5);
                v_canUnfold_x3f_6321_ = crate::leanh::lean_ctor_get(v___y_6243_, 6);
                v_univApprox_6322_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_6243_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_6323_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_6243_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_6324_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_6243_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_6325_ = 1;
                if v_isShared_6314_ == 0 {
                    v_config_6327_ = v___x_6313_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6357_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6357_,
                        0 as u32,
                        v_foApprox_6294_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6357_,
                        1 as u32,
                        v_ctxApprox_6295_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6357_,
                        2 as u32,
                        v_quasiPatternApprox_6296_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6357_,
                        3 as u32,
                        v_constApprox_6297_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6357_,
                        4 as u32,
                        v_isDefEqStuckEx_6298_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6357_,
                        5 as u32,
                        v_unificationHints_6299_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6357_,
                        6 as u32,
                        v_proofIrrelevance_6300_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6357_,
                        7 as u32,
                        v_assignSyntheticOpaque_6301_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6357_,
                        8 as u32,
                        v_offsetCnstrs_6302_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6357_,
                        10 as u32,
                        v_etaStruct_6303_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6357_,
                        11 as u32,
                        v_univApprox_6304_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6357_,
                        12 as u32,
                        v_iota_6305_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6357_,
                        13 as u32,
                        v_beta_6306_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6357_,
                        14 as u32,
                        v_proj_6307_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6357_,
                        15 as u32,
                        v_zeta_6308_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6357_,
                        16 as u32,
                        v_zetaDelta_6309_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6357_,
                        17 as u32,
                        v_zetaUnused_6310_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6357_,
                        18 as u32,
                        v_zetaHave_6311_,
                    );
                    v_config_6327_ = v_reuseFailAlloc_6357_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                crate::leanh::lean_ctor_set_uint8(v_config_6327_, 9 as u32, v___x_6325_);
                v___x_6328_ = l_Lean_Meta_Context_configKey(v___y_6243_);
                v___x_6329_ = 3u64;
                v___x_6330_ = lean_uint64_shift_right(v___x_6328_, v___x_6329_);
                v___x_6331_ = lean_array_fget(v_fieldNames_6264_, v_idx_6255_);
                crate::leanh::lean_dec(v_idx_6255_);
                crate::leanh::lean_dec_ref(v_fieldNames_6264_);
                v___x_6332_ = lean_uint64_shift_left(v___x_6330_, v___x_6329_);
                v___x_6333_ = crate::leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_foldProjs___lam__0___closed__10),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_foldProjs___lam__0___closed__10_once),
                    _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__10,
                );
                v_key_6334_ = lean_uint64_lor(v___x_6332_, v___x_6333_);
                v___x_6335_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_6335_, 0, v_config_6327_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_6335_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_6334_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_6321_);
                crate::leanh::lean_inc(v_synthPendingDepth_6320_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_6319_);
                crate::leanh::lean_inc_ref(v_localInstances_6318_);
                crate::leanh::lean_inc_ref(v_lctx_6317_);
                crate::leanh::lean_inc(v_zetaDeltaSet_6316_);
                v___x_6336_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_6336_, 0, v___x_6335_);
                crate::leanh::lean_ctor_set(v___x_6336_, 1, v_zetaDeltaSet_6316_);
                crate::leanh::lean_ctor_set(v___x_6336_, 2, v_lctx_6317_);
                crate::leanh::lean_ctor_set(v___x_6336_, 3, v_localInstances_6318_);
                crate::leanh::lean_ctor_set(v___x_6336_, 4, v_defEqCtx_x3f_6319_);
                crate::leanh::lean_ctor_set(v___x_6336_, 5, v_synthPendingDepth_6320_);
                crate::leanh::lean_ctor_set(v___x_6336_, 6, v_canUnfold_x3f_6321_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6336_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_6315_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6336_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_6322_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6336_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_6323_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6336_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_6324_,
                );
                v___x_6337_ = l_Lean_Meta_mkProjection(
                    v_struct_6256_,
                    v___x_6331_,
                    v___x_6336_,
                    v___y_6244_,
                    v___y_6245_,
                    v___y_6246_,
                );
                crate::leanh::lean_dec_ref_known(v___x_6336_, 7);
                if crate::leanh::lean_obj_tag(v___x_6337_) == 0 {
                    v_a_6338_ = crate::leanh::lean_ctor_get(v___x_6337_, 0);
                    v_isSharedCheck_6348_ = (!crate::leanh::lean_is_exclusive(v___x_6337_)) as u8;
                    if v_isSharedCheck_6348_ == 0 {
                        v___x_6340_ = v___x_6337_;
                        v_isShared_6341_ = v_isSharedCheck_6348_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6338_);
                        crate::leanh::lean_dec(v___x_6337_);
                        v___x_6340_ = crate::leanh::lean_box(0);
                        v_isShared_6341_ = v_isSharedCheck_6348_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6262_);
                    v_a_6349_ = crate::leanh::lean_ctor_get(v___x_6337_, 0);
                    v_isSharedCheck_6356_ = (!crate::leanh::lean_is_exclusive(v___x_6337_)) as u8;
                    if v_isSharedCheck_6356_ == 0 {
                        v___x_6351_ = v___x_6337_;
                        v_isShared_6352_ = v_isSharedCheck_6356_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6349_);
                        crate::leanh::lean_dec(v___x_6337_);
                        v___x_6351_ = crate::leanh::lean_box(0);
                        v_isShared_6352_ = v_isSharedCheck_6356_;
                        state = 12;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_6263_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6262_, 0, v_a_6338_);
                    v___x_6343_ = v___x_6262_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6347_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6347_, 0, v_a_6338_);
                    v___x_6343_ = v_reuseFailAlloc_6347_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_6341_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6340_, 0, v___x_6343_);
                    v___x_6345_ = v___x_6340_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6346_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6346_, 0, v___x_6343_);
                    v___x_6345_ = v_reuseFailAlloc_6346_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6345_;
            }
            12 => {
                if v_isShared_6352_ == 0 {
                    v___x_6354_ = v___x_6351_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6355_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6355_, 0, v_a_6349_);
                    v___x_6354_ = v_reuseFailAlloc_6355_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6354_;
            }
            14 => {
                if v_isShared_6377_ == 0 {
                    v___x_6379_ = v___x_6376_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6380_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6380_, 0, v_a_6374_);
                    v___x_6379_ = v_reuseFailAlloc_6380_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6379_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_foldProjs___lam__0___boxed(
    mut v_e_6384_: *mut crate::leanh::LeanObject,
    mut v___y_6385_: *mut crate::leanh::LeanObject,
    mut v___y_6386_: *mut crate::leanh::LeanObject,
    mut v___y_6387_: *mut crate::leanh::LeanObject,
    mut v___y_6388_: *mut crate::leanh::LeanObject,
    mut v___y_6389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6390_ = l_Lean_Meta_Sym_foldProjs___lam__0(
        v_e_6384_,
        v___y_6385_,
        v___y_6386_,
        v___y_6387_,
        v___y_6388_,
    );
    crate::leanh::lean_dec(v___y_6388_);
    crate::leanh::lean_dec_ref(v___y_6387_);
    crate::leanh::lean_dec(v___y_6386_);
    crate::leanh::lean_dec_ref(v___y_6385_);
    return v_res_6390_;
}
pub unsafe fn l_Lean_Meta_Sym_foldProjs___lam__1(
    mut v_x_6391_: *mut crate::leanh::LeanObject,
    mut v___y_6392_: *mut crate::leanh::LeanObject,
    mut v___y_6393_: *mut crate::leanh::LeanObject,
    mut v___y_6394_: *mut crate::leanh::LeanObject,
    mut v___y_6395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6397_ = l_Lean_Meta_Sym_unfoldReducibleStep___closed__0;
    v___x_6398_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6398_, 0, v___x_6397_);
    return v___x_6398_;
}
pub unsafe fn l_Lean_Meta_Sym_foldProjs___lam__1___boxed(
    mut v_x_6399_: *mut crate::leanh::LeanObject,
    mut v___y_6400_: *mut crate::leanh::LeanObject,
    mut v___y_6401_: *mut crate::leanh::LeanObject,
    mut v___y_6402_: *mut crate::leanh::LeanObject,
    mut v___y_6403_: *mut crate::leanh::LeanObject,
    mut v___y_6404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6405_ = l_Lean_Meta_Sym_foldProjs___lam__1(
        v_x_6399_,
        v___y_6400_,
        v___y_6401_,
        v___y_6402_,
        v___y_6403_,
    );
    crate::leanh::lean_dec(v___y_6403_);
    crate::leanh::lean_dec_ref(v___y_6402_);
    crate::leanh::lean_dec(v___y_6401_);
    crate::leanh::lean_dec_ref(v___y_6400_);
    crate::leanh::lean_dec_ref(v_x_6399_);
    return v_res_6405_;
}
pub unsafe fn l_Lean_Meta_Sym_foldProjs(
    mut v_e_6409_: *mut crate::leanh::LeanObject,
    mut v_a_6410_: *mut crate::leanh::LeanObject,
    mut v_a_6411_: *mut crate::leanh::LeanObject,
    mut v_a_6412_: *mut crate::leanh::LeanObject,
    mut v_a_6413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6415_ = l_Lean_Meta_Sym_foldProjs___closed__0;
    v___x_6416_ = lean_find_expr(v___f_6415_, v_e_6409_);
    if crate::leanh::lean_obj_tag(v___x_6416_) == 0 {
        let mut v___x_6417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6417_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6417_, 0, v_e_6409_);
        return v___x_6417_;
    } else {
        let mut v_post_6418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6420_: u8 = 0;
        let mut v___x_6421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_6416_, 1);
        v_post_6418_ = l_Lean_Meta_Sym_foldProjs___closed__1;
        v___f_6419_ = l_Lean_Meta_Sym_foldProjs___closed__2;
        v___x_6420_ = 0;
        v___x_6421_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(
            v_e_6409_,
            v___f_6419_,
            v_post_6418_,
            v___x_6420_,
            v___x_6420_,
            v_a_6410_,
            v_a_6411_,
            v_a_6412_,
            v_a_6413_,
        );
        return v___x_6421_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_foldProjs___boxed(
    mut v_e_6422_: *mut crate::leanh::LeanObject,
    mut v_a_6423_: *mut crate::leanh::LeanObject,
    mut v_a_6424_: *mut crate::leanh::LeanObject,
    mut v_a_6425_: *mut crate::leanh::LeanObject,
    mut v_a_6426_: *mut crate::leanh::LeanObject,
    mut v_a_6427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6428_ = l_Lean_Meta_Sym_foldProjs(v_e_6422_, v_a_6423_, v_a_6424_, v_a_6425_, v_a_6426_);
    crate::leanh::lean_dec(v_a_6426_);
    crate::leanh::lean_dec_ref(v_a_6425_);
    crate::leanh::lean_dec(v_a_6424_);
    crate::leanh::lean_dec_ref(v_a_6423_);
    return v_res_6428_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___redArg(
    mut v_e_6429_: *mut crate::leanh::LeanObject,
    mut v___y_6430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6432_: u8 = 0;
    let mut v___x_6433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_6442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6446_: u8 = 0;
    let mut v___x_6448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6452_: u8 = 0;
    let mut v_unused_6453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6432_ = l_Lean_Expr_hasMVar(v_e_6429_);
                if v___x_6432_ == 0 {
                    v___x_6433_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6433_, 0, v_e_6429_);
                    return v___x_6433_;
                } else {
                    v___x_6434_ = lean_st_ref_get(v___y_6430_);
                    v_mctx_6435_ = crate::leanh::lean_ctor_get(v___x_6434_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_6435_);
                    crate::leanh::lean_dec(v___x_6434_);
                    v___x_6436_ = l_Lean_instantiateMVarsCore(v_mctx_6435_, v_e_6429_);
                    v_fst_6437_ = crate::leanh::lean_ctor_get(v___x_6436_, 0);
                    crate::leanh::lean_inc(v_fst_6437_);
                    v_snd_6438_ = crate::leanh::lean_ctor_get(v___x_6436_, 1);
                    crate::leanh::lean_inc(v_snd_6438_);
                    crate::leanh::lean_dec_ref(v___x_6436_);
                    v___x_6439_ = lean_st_ref_take(v___y_6430_);
                    v_cache_6440_ = crate::leanh::lean_ctor_get(v___x_6439_, 1);
                    v_zetaDeltaFVarIds_6441_ = crate::leanh::lean_ctor_get(v___x_6439_, 2);
                    v_postponed_6442_ = crate::leanh::lean_ctor_get(v___x_6439_, 3);
                    v_diag_6443_ = crate::leanh::lean_ctor_get(v___x_6439_, 4);
                    v_isSharedCheck_6452_ = (!crate::leanh::lean_is_exclusive(v___x_6439_)) as u8;
                    if v_isSharedCheck_6452_ == 0 {
                        v_unused_6453_ = crate::leanh::lean_ctor_get(v___x_6439_, 0);
                        crate::leanh::lean_dec(v_unused_6453_);
                        v___x_6445_ = v___x_6439_;
                        v_isShared_6446_ = v_isSharedCheck_6452_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_6443_);
                        crate::leanh::lean_inc(v_postponed_6442_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_6441_);
                        crate::leanh::lean_inc(v_cache_6440_);
                        crate::leanh::lean_dec(v___x_6439_);
                        v___x_6445_ = crate::leanh::lean_box(0);
                        v_isShared_6446_ = v_isSharedCheck_6452_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6446_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6445_, 0, v_snd_6438_);
                    v___x_6448_ = v___x_6445_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6451_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6451_, 0, v_snd_6438_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6451_, 1, v_cache_6440_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_6451_,
                        2,
                        v_zetaDeltaFVarIds_6441_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6451_, 3, v_postponed_6442_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6451_, 4, v_diag_6443_);
                    v___x_6448_ = v_reuseFailAlloc_6451_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6449_ = lean_st_ref_set(v___y_6430_, v___x_6448_);
                v___x_6450_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6450_, 0, v_fst_6437_);
                return v___x_6450_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___redArg___boxed(
    mut v_e_6454_: *mut crate::leanh::LeanObject,
    mut v___y_6455_: *mut crate::leanh::LeanObject,
    mut v___y_6456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6457_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___redArg(v_e_6454_, v___y_6455_);
    crate::leanh::lean_dec(v___y_6455_);
    return v_res_6457_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0(
    mut v_e_6458_: *mut crate::leanh::LeanObject,
    mut v___y_6459_: *mut crate::leanh::LeanObject,
    mut v___y_6460_: *mut crate::leanh::LeanObject,
    mut v___y_6461_: *mut crate::leanh::LeanObject,
    mut v___y_6462_: *mut crate::leanh::LeanObject,
    mut v___y_6463_: *mut crate::leanh::LeanObject,
    mut v___y_6464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6466_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___redArg(v_e_6458_, v___y_6462_);
    return v___x_6466_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___boxed(
    mut v_e_6467_: *mut crate::leanh::LeanObject,
    mut v___y_6468_: *mut crate::leanh::LeanObject,
    mut v___y_6469_: *mut crate::leanh::LeanObject,
    mut v___y_6470_: *mut crate::leanh::LeanObject,
    mut v___y_6471_: *mut crate::leanh::LeanObject,
    mut v___y_6472_: *mut crate::leanh::LeanObject,
    mut v___y_6473_: *mut crate::leanh::LeanObject,
    mut v___y_6474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6475_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0(v_e_6467_, v___y_6468_, v___y_6469_, v___y_6470_, v___y_6471_, v___y_6472_, v___y_6473_);
    crate::leanh::lean_dec(v___y_6473_);
    crate::leanh::lean_dec_ref(v___y_6472_);
    crate::leanh::lean_dec(v___y_6471_);
    crate::leanh::lean_dec_ref(v___y_6470_);
    crate::leanh::lean_dec(v___y_6469_);
    crate::leanh::lean_dec_ref(v___y_6468_);
    return v_res_6475_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(
    mut v_e_6476_: *mut crate::leanh::LeanObject,
    mut v_a_6477_: *mut crate::leanh::LeanObject,
    mut v_a_6478_: *mut crate::leanh::LeanObject,
    mut v_a_6479_: *mut crate::leanh::LeanObject,
    mut v_a_6480_: *mut crate::leanh::LeanObject,
    mut v_a_6481_: *mut crate::leanh::LeanObject,
    mut v_a_6482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6484_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___redArg(v_e_6476_, v_a_6480_);
    v_a_6485_ = crate::leanh::lean_ctor_get(v___x_6484_, 0);
    crate::leanh::lean_inc(v_a_6485_);
    crate::leanh::lean_dec_ref(v___x_6484_);
    v___x_6486_ =
        l_Lean_Meta_Sym_unfoldReducible(v_a_6485_, v_a_6479_, v_a_6480_, v_a_6481_, v_a_6482_);
    if crate::leanh::lean_obj_tag(v___x_6486_) == 0 {
        let mut v_a_6487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_6487_ = crate::leanh::lean_ctor_get(v___x_6486_, 0);
        crate::leanh::lean_inc(v_a_6487_);
        crate::leanh::lean_dec_ref_known(v___x_6486_, 1);
        v___x_6488_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_6487_, v_a_6478_);
        return v___x_6488_;
    } else {
        return v___x_6486_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr___boxed(
    mut v_e_6489_: *mut crate::leanh::LeanObject,
    mut v_a_6490_: *mut crate::leanh::LeanObject,
    mut v_a_6491_: *mut crate::leanh::LeanObject,
    mut v_a_6492_: *mut crate::leanh::LeanObject,
    mut v_a_6493_: *mut crate::leanh::LeanObject,
    mut v_a_6494_: *mut crate::leanh::LeanObject,
    mut v_a_6495_: *mut crate::leanh::LeanObject,
    mut v_a_6496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6497_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(
        v_e_6489_, v_a_6490_, v_a_6491_, v_a_6492_, v_a_6493_, v_a_6494_, v_a_6495_,
    );
    crate::leanh::lean_dec(v_a_6495_);
    crate::leanh::lean_dec_ref(v_a_6494_);
    crate::leanh::lean_dec(v_a_6493_);
    crate::leanh::lean_dec_ref(v_a_6492_);
    crate::leanh::lean_dec(v_a_6491_);
    crate::leanh::lean_dec_ref(v_a_6490_);
    return v_res_6497_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_x_6498_: *mut crate::leanh::LeanObject,
    mut v_x_6499_: *mut crate::leanh::LeanObject,
    mut v_x_6500_: *mut crate::leanh::LeanObject,
    mut v_x_6501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_6502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6506_: u8 = 0;
    let mut v___x_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6508_: u8 = 0;
    let mut v___x_6509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_6514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6515_: u8 = 0;
    let mut v___x_6517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6527_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_6502_ = crate::leanh::lean_ctor_get(v_x_6498_, 0);
                v_vs_6503_ = crate::leanh::lean_ctor_get(v_x_6498_, 1);
                v_isSharedCheck_6527_ = (!crate::leanh::lean_is_exclusive(v_x_6498_)) as u8;
                if v_isSharedCheck_6527_ == 0 {
                    v___x_6505_ = v_x_6498_;
                    v_isShared_6506_ = v_isSharedCheck_6527_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_6503_);
                    crate::leanh::lean_inc(v_ks_6502_);
                    crate::leanh::lean_dec(v_x_6498_);
                    v___x_6505_ = crate::leanh::lean_box(0);
                    v_isShared_6506_ = v_isSharedCheck_6527_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6507_ = lean_array_get_size(v_ks_6502_);
                v___x_6508_ = lean_nat_dec_lt(v_x_6499_, v___x_6507_);
                if v___x_6508_ == 0 {
                    crate::leanh::lean_dec(v_x_6499_);
                    v___x_6509_ = lean_array_push(v_ks_6502_, v_x_6500_);
                    v___x_6510_ = lean_array_push(v_vs_6503_, v_x_6501_);
                    if v_isShared_6506_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6505_, 1, v___x_6510_);
                        crate::leanh::lean_ctor_set(v___x_6505_, 0, v___x_6509_);
                        v___x_6512_ = v___x_6505_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6513_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6513_, 0, v___x_6509_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6513_, 1, v___x_6510_);
                        v___x_6512_ = v_reuseFailAlloc_6513_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_6514_ = lean_array_fget_borrowed(v_ks_6502_, v_x_6499_);
                    v___x_6515_ = l_Lean_instBEqFVarId_beq(v_x_6500_, v_k_x27_6514_);
                    if v___x_6515_ == 0 {
                        if v_isShared_6506_ == 0 {
                            v___x_6517_ = v___x_6505_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6521_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6521_, 0, v_ks_6502_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6521_, 1, v_vs_6503_);
                            v___x_6517_ = v_reuseFailAlloc_6521_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_6522_ = lean_array_fset(v_ks_6502_, v_x_6499_, v_x_6500_);
                        v___x_6523_ = lean_array_fset(v_vs_6503_, v_x_6499_, v_x_6501_);
                        crate::leanh::lean_dec(v_x_6499_);
                        if v_isShared_6506_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6505_, 1, v___x_6523_);
                            crate::leanh::lean_ctor_set(v___x_6505_, 0, v___x_6522_);
                            v___x_6525_ = v___x_6505_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_6526_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6526_, 0, v___x_6522_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6526_, 1, v___x_6523_);
                            v___x_6525_ = v_reuseFailAlloc_6526_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_6512_;
            }
            3 => {
                v___x_6518_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6519_ = lean_nat_add(v_x_6499_, v___x_6518_);
                crate::leanh::lean_dec(v_x_6499_);
                v_x_6498_ = v___x_6517_;
                v_x_6499_ = v___x_6519_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_6525_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1___redArg(
    mut v_n_6528_: *mut crate::leanh::LeanObject,
    mut v_k_6529_: *mut crate::leanh::LeanObject,
    mut v_v_6530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6531_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6532_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3___redArg(v_n_6528_, v___x_6531_, v_k_6529_, v_v_6530_);
    return v___x_6532_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_6533_: usize = 0;
    let mut v___x_6534_: usize = 0;
    let mut v___x_6535_: usize = 0;
    v___x_6533_ = 5usize;
    v___x_6534_ = 1usize;
    v___x_6535_ = lean_usize_shift_left(v___x_6534_, v___x_6533_);
    return v___x_6535_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_6536_: usize = 0;
    let mut v___x_6537_: usize = 0;
    let mut v___x_6538_: usize = 0;
    v___x_6536_ = 1usize;
    v___x_6537_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0);
    v___x_6538_ = lean_usize_sub(v___x_6537_, v___x_6536_);
    return v___x_6538_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6539_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_6539_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(
    mut v_x_6540_: *mut crate::leanh::LeanObject,
    mut v_x_6541_: usize,
    mut v_x_6542_: usize,
    mut v_x_6543_: *mut crate::leanh::LeanObject,
    mut v_x_6544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_6545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: usize = 0;
    let mut v___x_6547_: usize = 0;
    let mut v___x_6548_: usize = 0;
    let mut v___x_6549_: usize = 0;
    let mut v_j_6550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6552_: u8 = 0;
    let mut v___x_6554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6555_: u8 = 0;
    let mut v_v_6556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_6565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6569_: u8 = 0;
    let mut v___x_6570_: u8 = 0;
    let mut v___x_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6576_: u8 = 0;
    let mut v_node_6577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6580_: u8 = 0;
    let mut v___x_6581_: usize = 0;
    let mut v___x_6582_: usize = 0;
    let mut v___x_6583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6587_: u8 = 0;
    let mut v___x_6588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6589_: u8 = 0;
    let mut v_unused_6590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_6591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_6592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6595_: u8 = 0;
    let mut v___x_6597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_6598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6600_: u8 = 0;
    let mut v_ks_6601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_6602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6606_: usize = 0;
    let mut v___x_6607_: u8 = 0;
    let mut v___x_6608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6610_: u8 = 0;
    let mut v_reuseFailAlloc_6611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6612_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6540_) == 0 {
                    v_es_6545_ = crate::leanh::lean_ctor_get(v_x_6540_, 0);
                    v___x_6546_ = 5usize;
                    v___x_6547_ = 1usize;
                    v___x_6548_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1);
                    v___x_6549_ = lean_usize_land(v_x_6541_, v___x_6548_);
                    v_j_6550_ = lean_usize_to_nat(v___x_6549_);
                    v___x_6551_ = lean_array_get_size(v_es_6545_);
                    v___x_6552_ = lean_nat_dec_lt(v_j_6550_, v___x_6551_);
                    if v___x_6552_ == 0 {
                        crate::leanh::lean_dec(v_j_6550_);
                        crate::leanh::lean_dec(v_x_6544_);
                        crate::leanh::lean_dec(v_x_6543_);
                        return v_x_6540_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_6545_);
                        v_isSharedCheck_6589_ = (!crate::leanh::lean_is_exclusive(v_x_6540_)) as u8;
                        if v_isSharedCheck_6589_ == 0 {
                            v_unused_6590_ = crate::leanh::lean_ctor_get(v_x_6540_, 0);
                            crate::leanh::lean_dec(v_unused_6590_);
                            v___x_6554_ = v_x_6540_;
                            v_isShared_6555_ = v_isSharedCheck_6589_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_6540_);
                            v___x_6554_ = crate::leanh::lean_box(0);
                            v_isShared_6555_ = v_isSharedCheck_6589_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_6591_ = crate::leanh::lean_ctor_get(v_x_6540_, 0);
                    v_vs_6592_ = crate::leanh::lean_ctor_get(v_x_6540_, 1);
                    v_isSharedCheck_6612_ = (!crate::leanh::lean_is_exclusive(v_x_6540_)) as u8;
                    if v_isSharedCheck_6612_ == 0 {
                        v___x_6594_ = v_x_6540_;
                        v_isShared_6595_ = v_isSharedCheck_6612_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_6592_);
                        crate::leanh::lean_inc(v_ks_6591_);
                        crate::leanh::lean_dec(v_x_6540_);
                        v___x_6594_ = crate::leanh::lean_box(0);
                        v_isShared_6595_ = v_isSharedCheck_6612_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_6556_ = lean_array_fget(v_es_6545_, v_j_6550_);
                v___x_6557_ = crate::leanh::lean_box(0);
                v_xs_x27_6558_ = lean_array_fset(v_es_6545_, v_j_6550_, v___x_6557_);
                match crate::leanh::lean_obj_tag(v_v_6556_) {
                    0 => {
                        v_key_6565_ = crate::leanh::lean_ctor_get(v_v_6556_, 0);
                        v_val_6566_ = crate::leanh::lean_ctor_get(v_v_6556_, 1);
                        v_isSharedCheck_6576_ = (!crate::leanh::lean_is_exclusive(v_v_6556_)) as u8;
                        if v_isSharedCheck_6576_ == 0 {
                            v___x_6568_ = v_v_6556_;
                            v_isShared_6569_ = v_isSharedCheck_6576_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_6566_);
                            crate::leanh::lean_inc(v_key_6565_);
                            crate::leanh::lean_dec(v_v_6556_);
                            v___x_6568_ = crate::leanh::lean_box(0);
                            v_isShared_6569_ = v_isSharedCheck_6576_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_6577_ = crate::leanh::lean_ctor_get(v_v_6556_, 0);
                        v_isSharedCheck_6587_ = (!crate::leanh::lean_is_exclusive(v_v_6556_)) as u8;
                        if v_isSharedCheck_6587_ == 0 {
                            v___x_6579_ = v_v_6556_;
                            v_isShared_6580_ = v_isSharedCheck_6587_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_6577_);
                            crate::leanh::lean_dec(v_v_6556_);
                            v___x_6579_ = crate::leanh::lean_box(0);
                            v_isShared_6580_ = v_isSharedCheck_6587_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_6588_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6588_, 0, v_x_6543_);
                        crate::leanh::lean_ctor_set(v___x_6588_, 1, v_x_6544_);
                        v___y_6560_ = v___x_6588_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6561_ = lean_array_fset(v_xs_x27_6558_, v_j_6550_, v___y_6560_);
                crate::leanh::lean_dec(v_j_6550_);
                if v_isShared_6555_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6554_, 0, v___x_6561_);
                    v___x_6563_ = v___x_6554_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6564_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6564_, 0, v___x_6561_);
                    v___x_6563_ = v_reuseFailAlloc_6564_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6563_;
            }
            4 => {
                v___x_6570_ = l_Lean_instBEqFVarId_beq(v_x_6543_, v_key_6565_);
                if v___x_6570_ == 0 {
                    crate::leanh::lean_del_object(v___x_6568_);
                    v___x_6571_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_6565_,
                        v_val_6566_,
                        v_x_6543_,
                        v_x_6544_,
                    );
                    v___x_6572_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6572_, 0, v___x_6571_);
                    v___y_6560_ = v___x_6572_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_6566_);
                    crate::leanh::lean_dec(v_key_6565_);
                    if v_isShared_6569_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6568_, 1, v_x_6544_);
                        crate::leanh::lean_ctor_set(v___x_6568_, 0, v_x_6543_);
                        v___x_6574_ = v___x_6568_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6575_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6575_, 0, v_x_6543_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6575_, 1, v_x_6544_);
                        v___x_6574_ = v_reuseFailAlloc_6575_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_6560_ = v___x_6574_;
                state = 2;
                continue;
            }
            6 => {
                v___x_6581_ = lean_usize_shift_right(v_x_6541_, v___x_6546_);
                v___x_6582_ = lean_usize_add(v_x_6542_, v___x_6547_);
                v___x_6583_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_node_6577_, v___x_6581_, v___x_6582_, v_x_6543_, v_x_6544_);
                if v_isShared_6580_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6579_, 0, v___x_6583_);
                    v___x_6585_ = v___x_6579_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6586_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6586_, 0, v___x_6583_);
                    v___x_6585_ = v_reuseFailAlloc_6586_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_6560_ = v___x_6585_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_6595_ == 0 {
                    v___x_6597_ = v___x_6594_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6611_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6611_, 0, v_ks_6591_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6611_, 1, v_vs_6592_);
                    v___x_6597_ = v_reuseFailAlloc_6611_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_6598_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1___redArg(v___x_6597_, v_x_6543_, v_x_6544_);
                v___x_6606_ = 7usize;
                v___x_6607_ = lean_usize_dec_le(v___x_6606_, v_x_6542_);
                if v___x_6607_ == 0 {
                    v___x_6608_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_6598_);
                    v___x_6609_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_6610_ = lean_nat_dec_lt(v___x_6608_, v___x_6609_);
                    crate::leanh::lean_dec(v___x_6608_);
                    v___y_6600_ = v___x_6610_;
                    state = 10;
                    continue;
                } else {
                    v___y_6600_ = v___x_6607_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_6600_ == 0 {
                    v_ks_6601_ = crate::leanh::lean_ctor_get(v_newNode_6598_, 0);
                    crate::leanh::lean_inc_ref(v_ks_6601_);
                    v_vs_6602_ = crate::leanh::lean_ctor_get(v_newNode_6598_, 1);
                    crate::leanh::lean_inc_ref(v_vs_6602_);
                    crate::leanh::lean_dec_ref(v_newNode_6598_);
                    v___x_6603_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_6604_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2);
                    v___x_6605_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(v_x_6542_, v_ks_6601_, v_vs_6602_, v___x_6603_, v___x_6604_);
                    crate::leanh::lean_dec_ref(v_vs_6602_);
                    crate::leanh::lean_dec_ref(v_ks_6601_);
                    return v___x_6605_;
                } else {
                    return v_newNode_6598_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(
    mut v_depth_6613_: usize,
    mut v_keys_6614_: *mut crate::leanh::LeanObject,
    mut v_vals_6615_: *mut crate::leanh::LeanObject,
    mut v_i_6616_: *mut crate::leanh::LeanObject,
    mut v_entries_6617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6619_: u8 = 0;
    let mut v_k_6620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6622_: u64 = 0;
    let mut v_h_6623_: usize = 0;
    let mut v___x_6624_: usize = 0;
    let mut v___x_6625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6626_: usize = 0;
    let mut v___x_6627_: usize = 0;
    let mut v___x_6628_: usize = 0;
    let mut v_h_6629_: usize = 0;
    let mut v___x_6630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6618_ = lean_array_get_size(v_keys_6614_);
                v___x_6619_ = lean_nat_dec_lt(v_i_6616_, v___x_6618_);
                if v___x_6619_ == 0 {
                    crate::leanh::lean_dec(v_i_6616_);
                    return v_entries_6617_;
                } else {
                    v_k_6620_ = lean_array_fget_borrowed(v_keys_6614_, v_i_6616_);
                    v_v_6621_ = lean_array_fget_borrowed(v_vals_6615_, v_i_6616_);
                    v___x_6622_ = l_Lean_instHashableFVarId_hash(v_k_6620_);
                    v_h_6623_ = lean_uint64_to_usize(v___x_6622_);
                    v___x_6624_ = 5usize;
                    v___x_6625_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6626_ = 1usize;
                    v___x_6627_ = lean_usize_sub(v_depth_6613_, v___x_6626_);
                    v___x_6628_ = lean_usize_mul(v___x_6624_, v___x_6627_);
                    v_h_6629_ = lean_usize_shift_right(v_h_6623_, v___x_6628_);
                    v___x_6630_ = lean_nat_add(v_i_6616_, v___x_6625_);
                    crate::leanh::lean_dec(v_i_6616_);
                    crate::leanh::lean_inc(v_v_6621_);
                    crate::leanh::lean_inc(v_k_6620_);
                    v___x_6631_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_entries_6617_, v_h_6629_, v_depth_6613_, v_k_6620_, v_v_6621_);
                    v_i_6616_ = v___x_6630_;
                    v_entries_6617_ = v___x_6631_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_depth_6633_: *mut crate::leanh::LeanObject,
    mut v_keys_6634_: *mut crate::leanh::LeanObject,
    mut v_vals_6635_: *mut crate::leanh::LeanObject,
    mut v_i_6636_: *mut crate::leanh::LeanObject,
    mut v_entries_6637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_6638_: usize = 0;
    let mut v_res_6639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_6638_ = crate::leanh::lean_unbox_usize(v_depth_6633_);
    crate::leanh::lean_dec(v_depth_6633_);
    v_res_6639_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(v_depth_boxed_6638_, v_keys_6634_, v_vals_6635_, v_i_6636_, v_entries_6637_);
    crate::leanh::lean_dec_ref(v_vals_6635_);
    crate::leanh::lean_dec_ref(v_keys_6634_);
    return v_res_6639_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___boxed(
    mut v_x_6640_: *mut crate::leanh::LeanObject,
    mut v_x_6641_: *mut crate::leanh::LeanObject,
    mut v_x_6642_: *mut crate::leanh::LeanObject,
    mut v_x_6643_: *mut crate::leanh::LeanObject,
    mut v_x_6644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_9235__boxed_6645_: usize = 0;
    let mut v_x_9236__boxed_6646_: usize = 0;
    let mut v_res_6647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_9235__boxed_6645_ = crate::leanh::lean_unbox_usize(v_x_6641_);
    crate::leanh::lean_dec(v_x_6641_);
    v_x_9236__boxed_6646_ = crate::leanh::lean_unbox_usize(v_x_6642_);
    crate::leanh::lean_dec(v_x_6642_);
    v_res_6647_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_x_6640_, v_x_9235__boxed_6645_, v_x_9236__boxed_6646_, v_x_6643_, v_x_6644_);
    return v_res_6647_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(
    mut v_x_6648_: *mut crate::leanh::LeanObject,
    mut v_x_6649_: *mut crate::leanh::LeanObject,
    mut v_x_6650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6651_: u64 = 0;
    let mut v___x_6652_: usize = 0;
    let mut v___x_6653_: usize = 0;
    let mut v___x_6654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6651_ = l_Lean_instHashableFVarId_hash(v_x_6649_);
    v___x_6652_ = lean_uint64_to_usize(v___x_6651_);
    v___x_6653_ = 1usize;
    v___x_6654_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_x_6648_, v___x_6652_, v___x_6653_, v_x_6649_, v_x_6650_);
    return v___x_6654_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8(
    mut v_as_6655_: *mut crate::leanh::LeanObject,
    mut v_sz_6656_: usize,
    mut v_i_6657_: usize,
    mut v_b_6658_: *mut crate::leanh::LeanObject,
    mut v___y_6659_: *mut crate::leanh::LeanObject,
    mut v___y_6660_: *mut crate::leanh::LeanObject,
    mut v___y_6661_: *mut crate::leanh::LeanObject,
    mut v___y_6662_: *mut crate::leanh::LeanObject,
    mut v___y_6663_: *mut crate::leanh::LeanObject,
    mut v___y_6664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6666_: u8 = 0;
    let mut v___x_6667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6671_: u8 = 0;
    let mut v___x_6672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: usize = 0;
    let mut v___x_6678_: usize = 0;
    let mut v_reuseFailAlloc_6680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6686_: u8 = 0;
    let mut v_fst_6687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6690_: u8 = 0;
    let mut v_fst_6691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6695_: u8 = 0;
    let mut v_decl_6697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_6713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bi_6715_: u8 = 0;
    let mut v_kind_6716_: u8 = 0;
    let mut v___x_6718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6719_: u8 = 0;
    let mut v___x_6720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6728_: u8 = 0;
    let mut v___x_6730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6732_: u8 = 0;
    let mut v_isSharedCheck_6733_: u8 = 0;
    let mut v_unused_6734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_6736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_6739_: u8 = 0;
    let mut v_kind_6740_: u8 = 0;
    let mut v___x_6742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6743_: u8 = 0;
    let mut v___x_6744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6754_: u8 = 0;
    let mut v___x_6756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6758_: u8 = 0;
    let mut v_a_6759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6762_: u8 = 0;
    let mut v___x_6764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6766_: u8 = 0;
    let mut v_isSharedCheck_6767_: u8 = 0;
    let mut v_unused_6768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6769_: u8 = 0;
    let mut v_isSharedCheck_6770_: u8 = 0;
    let mut v_unused_6771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6772_: u8 = 0;
    let mut v_isSharedCheck_6773_: u8 = 0;
    let mut v_unused_6774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6666_ = lean_usize_dec_lt(v_i_6657_, v_sz_6656_);
                if v___x_6666_ == 0 {
                    v___x_6667_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6667_, 0, v_b_6658_);
                    return v___x_6667_;
                } else {
                    v_snd_6668_ = crate::leanh::lean_ctor_get(v_b_6658_, 1);
                    v_isSharedCheck_6773_ = (!crate::leanh::lean_is_exclusive(v_b_6658_)) as u8;
                    if v_isSharedCheck_6773_ == 0 {
                        v_unused_6774_ = crate::leanh::lean_ctor_get(v_b_6658_, 0);
                        crate::leanh::lean_dec(v_unused_6774_);
                        v___x_6670_ = v_b_6658_;
                        v_isShared_6671_ = v_isSharedCheck_6773_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6668_);
                        crate::leanh::lean_dec(v_b_6658_);
                        v___x_6670_ = crate::leanh::lean_box(0);
                        v_isShared_6671_ = v_isSharedCheck_6773_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6672_ = crate::leanh::lean_box(0);
                v_a_6681_ = lean_array_uget(v_as_6655_, v_i_6657_);
                if crate::leanh::lean_obj_tag(v_a_6681_) == 0 {
                    v_a_6674_ = v_snd_6668_;
                    state = 2;
                    continue;
                } else {
                    v_snd_6682_ = crate::leanh::lean_ctor_get(v_snd_6668_, 1);
                    crate::leanh::lean_inc(v_snd_6682_);
                    v_val_6683_ = crate::leanh::lean_ctor_get(v_a_6681_, 0);
                    v_isSharedCheck_6772_ = (!crate::leanh::lean_is_exclusive(v_a_6681_)) as u8;
                    if v_isSharedCheck_6772_ == 0 {
                        v___x_6685_ = v_a_6681_;
                        v_isShared_6686_ = v_isSharedCheck_6772_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6683_);
                        crate::leanh::lean_dec(v_a_6681_);
                        v___x_6685_ = crate::leanh::lean_box(0);
                        v_isShared_6686_ = v_isSharedCheck_6772_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6671_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6670_, 1, v_a_6674_);
                    crate::leanh::lean_ctor_set(v___x_6670_, 0, v___x_6672_);
                    v___x_6676_ = v___x_6670_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6680_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6680_, 0, v___x_6672_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6680_, 1, v_a_6674_);
                    v___x_6676_ = v_reuseFailAlloc_6680_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6677_ = 1usize;
                v___x_6678_ = lean_usize_add(v_i_6657_, v___x_6677_);
                v_i_6657_ = v___x_6678_;
                v_b_6658_ = v___x_6676_;
                state = 0;
                continue;
            }
            4 => {
                v_fst_6687_ = crate::leanh::lean_ctor_get(v_snd_6668_, 0);
                v_isSharedCheck_6770_ = (!crate::leanh::lean_is_exclusive(v_snd_6668_)) as u8;
                if v_isSharedCheck_6770_ == 0 {
                    v_unused_6771_ = crate::leanh::lean_ctor_get(v_snd_6668_, 1);
                    crate::leanh::lean_dec(v_unused_6771_);
                    v___x_6689_ = v_snd_6668_;
                    v_isShared_6690_ = v_isSharedCheck_6770_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_6687_);
                    crate::leanh::lean_dec(v_snd_6668_);
                    v___x_6689_ = crate::leanh::lean_box(0);
                    v_isShared_6690_ = v_isSharedCheck_6770_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_fst_6691_ = crate::leanh::lean_ctor_get(v_snd_6682_, 0);
                v_snd_6692_ = crate::leanh::lean_ctor_get(v_snd_6682_, 1);
                v_isSharedCheck_6769_ = (!crate::leanh::lean_is_exclusive(v_snd_6682_)) as u8;
                if v_isSharedCheck_6769_ == 0 {
                    v___x_6694_ = v_snd_6682_;
                    v_isShared_6695_ = v_isSharedCheck_6769_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6692_);
                    crate::leanh::lean_inc(v_fst_6691_);
                    crate::leanh::lean_dec(v_snd_6682_);
                    v___x_6694_ = crate::leanh::lean_box(0);
                    v_isShared_6695_ = v_isSharedCheck_6769_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if crate::leanh::lean_obj_tag(v_val_6683_) == 0 {
                    v_fvarId_6712_ = crate::leanh::lean_ctor_get(v_val_6683_, 1);
                    v_userName_6713_ = crate::leanh::lean_ctor_get(v_val_6683_, 2);
                    v_type_6714_ = crate::leanh::lean_ctor_get(v_val_6683_, 3);
                    v_bi_6715_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_6683_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    v_kind_6716_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_6683_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                    );
                    v_isSharedCheck_6733_ = (!crate::leanh::lean_is_exclusive(v_val_6683_)) as u8;
                    if v_isSharedCheck_6733_ == 0 {
                        v_unused_6734_ = crate::leanh::lean_ctor_get(v_val_6683_, 0);
                        crate::leanh::lean_dec(v_unused_6734_);
                        v___x_6718_ = v_val_6683_;
                        v_isShared_6719_ = v_isSharedCheck_6733_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_type_6714_);
                        crate::leanh::lean_inc(v_userName_6713_);
                        crate::leanh::lean_inc(v_fvarId_6712_);
                        crate::leanh::lean_dec(v_val_6683_);
                        v___x_6718_ = crate::leanh::lean_box(0);
                        v_isShared_6719_ = v_isSharedCheck_6733_;
                        state = 11;
                        continue;
                    }
                } else {
                    v_fvarId_6735_ = crate::leanh::lean_ctor_get(v_val_6683_, 1);
                    v_userName_6736_ = crate::leanh::lean_ctor_get(v_val_6683_, 2);
                    v_type_6737_ = crate::leanh::lean_ctor_get(v_val_6683_, 3);
                    v_value_6738_ = crate::leanh::lean_ctor_get(v_val_6683_, 4);
                    v_nondep_6739_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_6683_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    );
                    v_kind_6740_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_6683_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    );
                    v_isSharedCheck_6767_ = (!crate::leanh::lean_is_exclusive(v_val_6683_)) as u8;
                    if v_isSharedCheck_6767_ == 0 {
                        v_unused_6768_ = crate::leanh::lean_ctor_get(v_val_6683_, 0);
                        crate::leanh::lean_dec(v_unused_6768_);
                        v___x_6742_ = v_val_6683_;
                        v_isShared_6743_ = v_isSharedCheck_6767_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_6738_);
                        crate::leanh::lean_inc(v_type_6737_);
                        crate::leanh::lean_inc(v_userName_6736_);
                        crate::leanh::lean_inc(v_fvarId_6735_);
                        crate::leanh::lean_dec(v_val_6683_);
                        v___x_6742_ = crate::leanh::lean_box(0);
                        v_isShared_6743_ = v_isSharedCheck_6767_;
                        state = 15;
                        continue;
                    }
                }
            }
            7 => {
                v___x_6698_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6699_ = lean_nat_add(v_snd_6692_, v___x_6698_);
                crate::leanh::lean_dec(v_snd_6692_);
                crate::leanh::lean_inc_ref(v_decl_6697_);
                if v_isShared_6686_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6685_, 0, v_decl_6697_);
                    v___x_6701_ = v___x_6685_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6711_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6711_, 0, v_decl_6697_);
                    v___x_6701_ = v_reuseFailAlloc_6711_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_6702_ = l_Lean_PersistentArray_push___redArg(v_fst_6691_, v___x_6701_);
                v___x_6703_ = l_Lean_LocalDecl_fvarId(v_decl_6697_);
                v___x_6704_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_6687_, v___x_6703_, v_decl_6697_);
                if v_isShared_6695_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6694_, 1, v___x_6699_);
                    crate::leanh::lean_ctor_set(v___x_6694_, 0, v___x_6702_);
                    v___x_6706_ = v___x_6694_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6710_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6710_, 0, v___x_6702_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6710_, 1, v___x_6699_);
                    v___x_6706_ = v_reuseFailAlloc_6710_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_6690_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6689_, 1, v___x_6706_);
                    crate::leanh::lean_ctor_set(v___x_6689_, 0, v___x_6704_);
                    v___x_6708_ = v___x_6689_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6709_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6709_, 0, v___x_6704_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6709_, 1, v___x_6706_);
                    v___x_6708_ = v_reuseFailAlloc_6709_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_a_6674_ = v___x_6708_;
                state = 2;
                continue;
            }
            11 => {
                v___x_6720_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(
                    v_type_6714_,
                    v___y_6659_,
                    v___y_6660_,
                    v___y_6661_,
                    v___y_6662_,
                    v___y_6663_,
                    v___y_6664_,
                );
                if crate::leanh::lean_obj_tag(v___x_6720_) == 0 {
                    v_a_6721_ = crate::leanh::lean_ctor_get(v___x_6720_, 0);
                    crate::leanh::lean_inc(v_a_6721_);
                    crate::leanh::lean_dec_ref_known(v___x_6720_, 1);
                    crate::leanh::lean_inc(v_snd_6692_);
                    if v_isShared_6719_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6718_, 3, v_a_6721_);
                        crate::leanh::lean_ctor_set(v___x_6718_, 0, v_snd_6692_);
                        v___x_6723_ = v___x_6718_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_6724_ = crate::leanh::lean_alloc_ctor(0, 4, (2) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6724_, 0, v_snd_6692_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6724_, 1, v_fvarId_6712_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6724_, 2, v_userName_6713_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6724_, 3, v_a_6721_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_6724_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            v_bi_6715_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_6724_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                            v_kind_6716_,
                        );
                        v___x_6723_ = v_reuseFailAlloc_6724_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6718_);
                    crate::leanh::lean_dec(v_userName_6713_);
                    crate::leanh::lean_dec(v_fvarId_6712_);
                    crate::leanh::lean_del_object(v___x_6694_);
                    crate::leanh::lean_dec(v_snd_6692_);
                    crate::leanh::lean_dec(v_fst_6691_);
                    crate::leanh::lean_del_object(v___x_6689_);
                    crate::leanh::lean_dec(v_fst_6687_);
                    crate::leanh::lean_del_object(v___x_6685_);
                    crate::leanh::lean_del_object(v___x_6670_);
                    v_a_6725_ = crate::leanh::lean_ctor_get(v___x_6720_, 0);
                    v_isSharedCheck_6732_ = (!crate::leanh::lean_is_exclusive(v___x_6720_)) as u8;
                    if v_isSharedCheck_6732_ == 0 {
                        v___x_6727_ = v___x_6720_;
                        v_isShared_6728_ = v_isSharedCheck_6732_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6725_);
                        crate::leanh::lean_dec(v___x_6720_);
                        v___x_6727_ = crate::leanh::lean_box(0);
                        v_isShared_6728_ = v_isSharedCheck_6732_;
                        state = 13;
                        continue;
                    }
                }
            }
            12 => {
                v_decl_6697_ = v___x_6723_;
                state = 7;
                continue;
            }
            13 => {
                if v_isShared_6728_ == 0 {
                    v___x_6730_ = v___x_6727_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6731_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6731_, 0, v_a_6725_);
                    v___x_6730_ = v_reuseFailAlloc_6731_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6730_;
            }
            15 => {
                v___x_6744_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(
                    v_type_6737_,
                    v___y_6659_,
                    v___y_6660_,
                    v___y_6661_,
                    v___y_6662_,
                    v___y_6663_,
                    v___y_6664_,
                );
                if crate::leanh::lean_obj_tag(v___x_6744_) == 0 {
                    v_a_6745_ = crate::leanh::lean_ctor_get(v___x_6744_, 0);
                    crate::leanh::lean_inc(v_a_6745_);
                    crate::leanh::lean_dec_ref_known(v___x_6744_, 1);
                    v___x_6746_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(
                        v_value_6738_,
                        v___y_6659_,
                        v___y_6660_,
                        v___y_6661_,
                        v___y_6662_,
                        v___y_6663_,
                        v___y_6664_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6746_) == 0 {
                        v_a_6747_ = crate::leanh::lean_ctor_get(v___x_6746_, 0);
                        crate::leanh::lean_inc(v_a_6747_);
                        crate::leanh::lean_dec_ref_known(v___x_6746_, 1);
                        crate::leanh::lean_inc(v_snd_6692_);
                        if v_isShared_6743_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6742_, 4, v_a_6747_);
                            crate::leanh::lean_ctor_set(v___x_6742_, 3, v_a_6745_);
                            crate::leanh::lean_ctor_set(v___x_6742_, 0, v_snd_6692_);
                            v___x_6749_ = v___x_6742_;
                            state = 16;
                            continue;
                        } else {
                            v_reuseFailAlloc_6750_ =
                                crate::leanh::lean_alloc_ctor(1, 5, (2) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6750_, 0, v_snd_6692_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6750_, 1, v_fvarId_6735_);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_6750_,
                                2,
                                v_userName_6736_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6750_, 3, v_a_6745_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6750_, 4, v_a_6747_);
                            crate::leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_6750_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                                v_nondep_6739_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_6750_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1)
                                    as u32,
                                v_kind_6740_,
                            );
                            v___x_6749_ = v_reuseFailAlloc_6750_;
                            state = 16;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6745_);
                        crate::leanh::lean_del_object(v___x_6742_);
                        crate::leanh::lean_dec(v_userName_6736_);
                        crate::leanh::lean_dec(v_fvarId_6735_);
                        crate::leanh::lean_del_object(v___x_6694_);
                        crate::leanh::lean_dec(v_snd_6692_);
                        crate::leanh::lean_dec(v_fst_6691_);
                        crate::leanh::lean_del_object(v___x_6689_);
                        crate::leanh::lean_dec(v_fst_6687_);
                        crate::leanh::lean_del_object(v___x_6685_);
                        crate::leanh::lean_del_object(v___x_6670_);
                        v_a_6751_ = crate::leanh::lean_ctor_get(v___x_6746_, 0);
                        v_isSharedCheck_6758_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6746_)) as u8;
                        if v_isSharedCheck_6758_ == 0 {
                            v___x_6753_ = v___x_6746_;
                            v_isShared_6754_ = v_isSharedCheck_6758_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6751_);
                            crate::leanh::lean_dec(v___x_6746_);
                            v___x_6753_ = crate::leanh::lean_box(0);
                            v_isShared_6754_ = v_isSharedCheck_6758_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6742_);
                    crate::leanh::lean_dec_ref(v_value_6738_);
                    crate::leanh::lean_dec(v_userName_6736_);
                    crate::leanh::lean_dec(v_fvarId_6735_);
                    crate::leanh::lean_del_object(v___x_6694_);
                    crate::leanh::lean_dec(v_snd_6692_);
                    crate::leanh::lean_dec(v_fst_6691_);
                    crate::leanh::lean_del_object(v___x_6689_);
                    crate::leanh::lean_dec(v_fst_6687_);
                    crate::leanh::lean_del_object(v___x_6685_);
                    crate::leanh::lean_del_object(v___x_6670_);
                    v_a_6759_ = crate::leanh::lean_ctor_get(v___x_6744_, 0);
                    v_isSharedCheck_6766_ = (!crate::leanh::lean_is_exclusive(v___x_6744_)) as u8;
                    if v_isSharedCheck_6766_ == 0 {
                        v___x_6761_ = v___x_6744_;
                        v_isShared_6762_ = v_isSharedCheck_6766_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6759_);
                        crate::leanh::lean_dec(v___x_6744_);
                        v___x_6761_ = crate::leanh::lean_box(0);
                        v_isShared_6762_ = v_isSharedCheck_6766_;
                        state = 19;
                        continue;
                    }
                }
            }
            16 => {
                v_decl_6697_ = v___x_6749_;
                state = 7;
                continue;
            }
            17 => {
                if v_isShared_6754_ == 0 {
                    v___x_6756_ = v___x_6753_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6757_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6757_, 0, v_a_6751_);
                    v___x_6756_ = v_reuseFailAlloc_6757_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_6756_;
            }
            19 => {
                if v_isShared_6762_ == 0 {
                    v___x_6764_ = v___x_6761_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_6765_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6765_, 0, v_a_6759_);
                    v___x_6764_ = v_reuseFailAlloc_6765_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_6764_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8___boxed(
    mut v_as_6775_: *mut crate::leanh::LeanObject,
    mut v_sz_6776_: *mut crate::leanh::LeanObject,
    mut v_i_6777_: *mut crate::leanh::LeanObject,
    mut v_b_6778_: *mut crate::leanh::LeanObject,
    mut v___y_6779_: *mut crate::leanh::LeanObject,
    mut v___y_6780_: *mut crate::leanh::LeanObject,
    mut v___y_6781_: *mut crate::leanh::LeanObject,
    mut v___y_6782_: *mut crate::leanh::LeanObject,
    mut v___y_6783_: *mut crate::leanh::LeanObject,
    mut v___y_6784_: *mut crate::leanh::LeanObject,
    mut v___y_6785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6786_: usize = 0;
    let mut v_i_boxed_6787_: usize = 0;
    let mut v_res_6788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6786_ = crate::leanh::lean_unbox_usize(v_sz_6776_);
    crate::leanh::lean_dec(v_sz_6776_);
    v_i_boxed_6787_ = crate::leanh::lean_unbox_usize(v_i_6777_);
    crate::leanh::lean_dec(v_i_6777_);
    v_res_6788_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8(v_as_6775_, v_sz_boxed_6786_, v_i_boxed_6787_, v_b_6778_, v___y_6779_, v___y_6780_, v___y_6781_, v___y_6782_, v___y_6783_, v___y_6784_);
    crate::leanh::lean_dec(v___y_6784_);
    crate::leanh::lean_dec_ref(v___y_6783_);
    crate::leanh::lean_dec(v___y_6782_);
    crate::leanh::lean_dec_ref(v___y_6781_);
    crate::leanh::lean_dec(v___y_6780_);
    crate::leanh::lean_dec_ref(v___y_6779_);
    crate::leanh::lean_dec_ref(v_as_6775_);
    return v_res_6788_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(
    mut v_as_6789_: *mut crate::leanh::LeanObject,
    mut v_sz_6790_: usize,
    mut v_i_6791_: usize,
    mut v_b_6792_: *mut crate::leanh::LeanObject,
    mut v___y_6793_: *mut crate::leanh::LeanObject,
    mut v___y_6794_: *mut crate::leanh::LeanObject,
    mut v___y_6795_: *mut crate::leanh::LeanObject,
    mut v___y_6796_: *mut crate::leanh::LeanObject,
    mut v___y_6797_: *mut crate::leanh::LeanObject,
    mut v___y_6798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6800_: u8 = 0;
    let mut v___x_6801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6805_: u8 = 0;
    let mut v___x_6806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6811_: usize = 0;
    let mut v___x_6812_: usize = 0;
    let mut v___x_6813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6820_: u8 = 0;
    let mut v_fst_6821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6824_: u8 = 0;
    let mut v_fst_6825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6829_: u8 = 0;
    let mut v_decl_6831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_6847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bi_6849_: u8 = 0;
    let mut v_kind_6850_: u8 = 0;
    let mut v___x_6852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6853_: u8 = 0;
    let mut v___x_6854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6862_: u8 = 0;
    let mut v___x_6864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6866_: u8 = 0;
    let mut v_isSharedCheck_6867_: u8 = 0;
    let mut v_unused_6868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_6870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_6873_: u8 = 0;
    let mut v_kind_6874_: u8 = 0;
    let mut v___x_6876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6877_: u8 = 0;
    let mut v___x_6878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6888_: u8 = 0;
    let mut v___x_6890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6892_: u8 = 0;
    let mut v_a_6893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6896_: u8 = 0;
    let mut v___x_6898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6900_: u8 = 0;
    let mut v_isSharedCheck_6901_: u8 = 0;
    let mut v_unused_6902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6903_: u8 = 0;
    let mut v_isSharedCheck_6904_: u8 = 0;
    let mut v_unused_6905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6906_: u8 = 0;
    let mut v_isSharedCheck_6907_: u8 = 0;
    let mut v_unused_6908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6800_ = lean_usize_dec_lt(v_i_6791_, v_sz_6790_);
                if v___x_6800_ == 0 {
                    v___x_6801_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6801_, 0, v_b_6792_);
                    return v___x_6801_;
                } else {
                    v_snd_6802_ = crate::leanh::lean_ctor_get(v_b_6792_, 1);
                    v_isSharedCheck_6907_ = (!crate::leanh::lean_is_exclusive(v_b_6792_)) as u8;
                    if v_isSharedCheck_6907_ == 0 {
                        v_unused_6908_ = crate::leanh::lean_ctor_get(v_b_6792_, 0);
                        crate::leanh::lean_dec(v_unused_6908_);
                        v___x_6804_ = v_b_6792_;
                        v_isShared_6805_ = v_isSharedCheck_6907_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6802_);
                        crate::leanh::lean_dec(v_b_6792_);
                        v___x_6804_ = crate::leanh::lean_box(0);
                        v_isShared_6805_ = v_isSharedCheck_6907_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6806_ = crate::leanh::lean_box(0);
                v_a_6815_ = lean_array_uget(v_as_6789_, v_i_6791_);
                if crate::leanh::lean_obj_tag(v_a_6815_) == 0 {
                    v_a_6808_ = v_snd_6802_;
                    state = 2;
                    continue;
                } else {
                    v_snd_6816_ = crate::leanh::lean_ctor_get(v_snd_6802_, 1);
                    crate::leanh::lean_inc(v_snd_6816_);
                    v_val_6817_ = crate::leanh::lean_ctor_get(v_a_6815_, 0);
                    v_isSharedCheck_6906_ = (!crate::leanh::lean_is_exclusive(v_a_6815_)) as u8;
                    if v_isSharedCheck_6906_ == 0 {
                        v___x_6819_ = v_a_6815_;
                        v_isShared_6820_ = v_isSharedCheck_6906_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6817_);
                        crate::leanh::lean_dec(v_a_6815_);
                        v___x_6819_ = crate::leanh::lean_box(0);
                        v_isShared_6820_ = v_isSharedCheck_6906_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6805_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6804_, 1, v_a_6808_);
                    crate::leanh::lean_ctor_set(v___x_6804_, 0, v___x_6806_);
                    v___x_6810_ = v___x_6804_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6814_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6814_, 0, v___x_6806_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6814_, 1, v_a_6808_);
                    v___x_6810_ = v_reuseFailAlloc_6814_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6811_ = 1usize;
                v___x_6812_ = lean_usize_add(v_i_6791_, v___x_6811_);
                v___x_6813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8(v_as_6789_, v_sz_6790_, v___x_6812_, v___x_6810_, v___y_6793_, v___y_6794_, v___y_6795_, v___y_6796_, v___y_6797_, v___y_6798_);
                return v___x_6813_;
            }
            4 => {
                v_fst_6821_ = crate::leanh::lean_ctor_get(v_snd_6802_, 0);
                v_isSharedCheck_6904_ = (!crate::leanh::lean_is_exclusive(v_snd_6802_)) as u8;
                if v_isSharedCheck_6904_ == 0 {
                    v_unused_6905_ = crate::leanh::lean_ctor_get(v_snd_6802_, 1);
                    crate::leanh::lean_dec(v_unused_6905_);
                    v___x_6823_ = v_snd_6802_;
                    v_isShared_6824_ = v_isSharedCheck_6904_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_6821_);
                    crate::leanh::lean_dec(v_snd_6802_);
                    v___x_6823_ = crate::leanh::lean_box(0);
                    v_isShared_6824_ = v_isSharedCheck_6904_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_fst_6825_ = crate::leanh::lean_ctor_get(v_snd_6816_, 0);
                v_snd_6826_ = crate::leanh::lean_ctor_get(v_snd_6816_, 1);
                v_isSharedCheck_6903_ = (!crate::leanh::lean_is_exclusive(v_snd_6816_)) as u8;
                if v_isSharedCheck_6903_ == 0 {
                    v___x_6828_ = v_snd_6816_;
                    v_isShared_6829_ = v_isSharedCheck_6903_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6826_);
                    crate::leanh::lean_inc(v_fst_6825_);
                    crate::leanh::lean_dec(v_snd_6816_);
                    v___x_6828_ = crate::leanh::lean_box(0);
                    v_isShared_6829_ = v_isSharedCheck_6903_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if crate::leanh::lean_obj_tag(v_val_6817_) == 0 {
                    v_fvarId_6846_ = crate::leanh::lean_ctor_get(v_val_6817_, 1);
                    v_userName_6847_ = crate::leanh::lean_ctor_get(v_val_6817_, 2);
                    v_type_6848_ = crate::leanh::lean_ctor_get(v_val_6817_, 3);
                    v_bi_6849_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_6817_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    v_kind_6850_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_6817_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                    );
                    v_isSharedCheck_6867_ = (!crate::leanh::lean_is_exclusive(v_val_6817_)) as u8;
                    if v_isSharedCheck_6867_ == 0 {
                        v_unused_6868_ = crate::leanh::lean_ctor_get(v_val_6817_, 0);
                        crate::leanh::lean_dec(v_unused_6868_);
                        v___x_6852_ = v_val_6817_;
                        v_isShared_6853_ = v_isSharedCheck_6867_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_type_6848_);
                        crate::leanh::lean_inc(v_userName_6847_);
                        crate::leanh::lean_inc(v_fvarId_6846_);
                        crate::leanh::lean_dec(v_val_6817_);
                        v___x_6852_ = crate::leanh::lean_box(0);
                        v_isShared_6853_ = v_isSharedCheck_6867_;
                        state = 11;
                        continue;
                    }
                } else {
                    v_fvarId_6869_ = crate::leanh::lean_ctor_get(v_val_6817_, 1);
                    v_userName_6870_ = crate::leanh::lean_ctor_get(v_val_6817_, 2);
                    v_type_6871_ = crate::leanh::lean_ctor_get(v_val_6817_, 3);
                    v_value_6872_ = crate::leanh::lean_ctor_get(v_val_6817_, 4);
                    v_nondep_6873_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_6817_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    );
                    v_kind_6874_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_6817_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    );
                    v_isSharedCheck_6901_ = (!crate::leanh::lean_is_exclusive(v_val_6817_)) as u8;
                    if v_isSharedCheck_6901_ == 0 {
                        v_unused_6902_ = crate::leanh::lean_ctor_get(v_val_6817_, 0);
                        crate::leanh::lean_dec(v_unused_6902_);
                        v___x_6876_ = v_val_6817_;
                        v_isShared_6877_ = v_isSharedCheck_6901_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_6872_);
                        crate::leanh::lean_inc(v_type_6871_);
                        crate::leanh::lean_inc(v_userName_6870_);
                        crate::leanh::lean_inc(v_fvarId_6869_);
                        crate::leanh::lean_dec(v_val_6817_);
                        v___x_6876_ = crate::leanh::lean_box(0);
                        v_isShared_6877_ = v_isSharedCheck_6901_;
                        state = 15;
                        continue;
                    }
                }
            }
            7 => {
                v___x_6832_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6833_ = lean_nat_add(v_snd_6826_, v___x_6832_);
                crate::leanh::lean_dec(v_snd_6826_);
                crate::leanh::lean_inc_ref(v_decl_6831_);
                if v_isShared_6820_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6819_, 0, v_decl_6831_);
                    v___x_6835_ = v___x_6819_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6845_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6845_, 0, v_decl_6831_);
                    v___x_6835_ = v_reuseFailAlloc_6845_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_6836_ = l_Lean_PersistentArray_push___redArg(v_fst_6825_, v___x_6835_);
                v___x_6837_ = l_Lean_LocalDecl_fvarId(v_decl_6831_);
                v___x_6838_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_6821_, v___x_6837_, v_decl_6831_);
                if v_isShared_6829_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6828_, 1, v___x_6833_);
                    crate::leanh::lean_ctor_set(v___x_6828_, 0, v___x_6836_);
                    v___x_6840_ = v___x_6828_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6844_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6844_, 0, v___x_6836_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6844_, 1, v___x_6833_);
                    v___x_6840_ = v_reuseFailAlloc_6844_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_6824_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6823_, 1, v___x_6840_);
                    crate::leanh::lean_ctor_set(v___x_6823_, 0, v___x_6838_);
                    v___x_6842_ = v___x_6823_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6843_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6843_, 0, v___x_6838_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6843_, 1, v___x_6840_);
                    v___x_6842_ = v_reuseFailAlloc_6843_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_a_6808_ = v___x_6842_;
                state = 2;
                continue;
            }
            11 => {
                v___x_6854_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(
                    v_type_6848_,
                    v___y_6793_,
                    v___y_6794_,
                    v___y_6795_,
                    v___y_6796_,
                    v___y_6797_,
                    v___y_6798_,
                );
                if crate::leanh::lean_obj_tag(v___x_6854_) == 0 {
                    v_a_6855_ = crate::leanh::lean_ctor_get(v___x_6854_, 0);
                    crate::leanh::lean_inc(v_a_6855_);
                    crate::leanh::lean_dec_ref_known(v___x_6854_, 1);
                    crate::leanh::lean_inc(v_snd_6826_);
                    if v_isShared_6853_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6852_, 3, v_a_6855_);
                        crate::leanh::lean_ctor_set(v___x_6852_, 0, v_snd_6826_);
                        v___x_6857_ = v___x_6852_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_6858_ = crate::leanh::lean_alloc_ctor(0, 4, (2) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6858_, 0, v_snd_6826_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6858_, 1, v_fvarId_6846_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6858_, 2, v_userName_6847_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6858_, 3, v_a_6855_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_6858_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            v_bi_6849_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_6858_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                            v_kind_6850_,
                        );
                        v___x_6857_ = v_reuseFailAlloc_6858_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6852_);
                    crate::leanh::lean_dec(v_userName_6847_);
                    crate::leanh::lean_dec(v_fvarId_6846_);
                    crate::leanh::lean_del_object(v___x_6828_);
                    crate::leanh::lean_dec(v_snd_6826_);
                    crate::leanh::lean_dec(v_fst_6825_);
                    crate::leanh::lean_del_object(v___x_6823_);
                    crate::leanh::lean_dec(v_fst_6821_);
                    crate::leanh::lean_del_object(v___x_6819_);
                    crate::leanh::lean_del_object(v___x_6804_);
                    v_a_6859_ = crate::leanh::lean_ctor_get(v___x_6854_, 0);
                    v_isSharedCheck_6866_ = (!crate::leanh::lean_is_exclusive(v___x_6854_)) as u8;
                    if v_isSharedCheck_6866_ == 0 {
                        v___x_6861_ = v___x_6854_;
                        v_isShared_6862_ = v_isSharedCheck_6866_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6859_);
                        crate::leanh::lean_dec(v___x_6854_);
                        v___x_6861_ = crate::leanh::lean_box(0);
                        v_isShared_6862_ = v_isSharedCheck_6866_;
                        state = 13;
                        continue;
                    }
                }
            }
            12 => {
                v_decl_6831_ = v___x_6857_;
                state = 7;
                continue;
            }
            13 => {
                if v_isShared_6862_ == 0 {
                    v___x_6864_ = v___x_6861_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6865_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6865_, 0, v_a_6859_);
                    v___x_6864_ = v_reuseFailAlloc_6865_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6864_;
            }
            15 => {
                v___x_6878_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(
                    v_type_6871_,
                    v___y_6793_,
                    v___y_6794_,
                    v___y_6795_,
                    v___y_6796_,
                    v___y_6797_,
                    v___y_6798_,
                );
                if crate::leanh::lean_obj_tag(v___x_6878_) == 0 {
                    v_a_6879_ = crate::leanh::lean_ctor_get(v___x_6878_, 0);
                    crate::leanh::lean_inc(v_a_6879_);
                    crate::leanh::lean_dec_ref_known(v___x_6878_, 1);
                    v___x_6880_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(
                        v_value_6872_,
                        v___y_6793_,
                        v___y_6794_,
                        v___y_6795_,
                        v___y_6796_,
                        v___y_6797_,
                        v___y_6798_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6880_) == 0 {
                        v_a_6881_ = crate::leanh::lean_ctor_get(v___x_6880_, 0);
                        crate::leanh::lean_inc(v_a_6881_);
                        crate::leanh::lean_dec_ref_known(v___x_6880_, 1);
                        crate::leanh::lean_inc(v_snd_6826_);
                        if v_isShared_6877_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6876_, 4, v_a_6881_);
                            crate::leanh::lean_ctor_set(v___x_6876_, 3, v_a_6879_);
                            crate::leanh::lean_ctor_set(v___x_6876_, 0, v_snd_6826_);
                            v___x_6883_ = v___x_6876_;
                            state = 16;
                            continue;
                        } else {
                            v_reuseFailAlloc_6884_ =
                                crate::leanh::lean_alloc_ctor(1, 5, (2) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6884_, 0, v_snd_6826_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6884_, 1, v_fvarId_6869_);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_6884_,
                                2,
                                v_userName_6870_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6884_, 3, v_a_6879_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6884_, 4, v_a_6881_);
                            crate::leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_6884_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                                v_nondep_6873_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_6884_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1)
                                    as u32,
                                v_kind_6874_,
                            );
                            v___x_6883_ = v_reuseFailAlloc_6884_;
                            state = 16;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6879_);
                        crate::leanh::lean_del_object(v___x_6876_);
                        crate::leanh::lean_dec(v_userName_6870_);
                        crate::leanh::lean_dec(v_fvarId_6869_);
                        crate::leanh::lean_del_object(v___x_6828_);
                        crate::leanh::lean_dec(v_snd_6826_);
                        crate::leanh::lean_dec(v_fst_6825_);
                        crate::leanh::lean_del_object(v___x_6823_);
                        crate::leanh::lean_dec(v_fst_6821_);
                        crate::leanh::lean_del_object(v___x_6819_);
                        crate::leanh::lean_del_object(v___x_6804_);
                        v_a_6885_ = crate::leanh::lean_ctor_get(v___x_6880_, 0);
                        v_isSharedCheck_6892_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6880_)) as u8;
                        if v_isSharedCheck_6892_ == 0 {
                            v___x_6887_ = v___x_6880_;
                            v_isShared_6888_ = v_isSharedCheck_6892_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6885_);
                            crate::leanh::lean_dec(v___x_6880_);
                            v___x_6887_ = crate::leanh::lean_box(0);
                            v_isShared_6888_ = v_isSharedCheck_6892_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6876_);
                    crate::leanh::lean_dec_ref(v_value_6872_);
                    crate::leanh::lean_dec(v_userName_6870_);
                    crate::leanh::lean_dec(v_fvarId_6869_);
                    crate::leanh::lean_del_object(v___x_6828_);
                    crate::leanh::lean_dec(v_snd_6826_);
                    crate::leanh::lean_dec(v_fst_6825_);
                    crate::leanh::lean_del_object(v___x_6823_);
                    crate::leanh::lean_dec(v_fst_6821_);
                    crate::leanh::lean_del_object(v___x_6819_);
                    crate::leanh::lean_del_object(v___x_6804_);
                    v_a_6893_ = crate::leanh::lean_ctor_get(v___x_6878_, 0);
                    v_isSharedCheck_6900_ = (!crate::leanh::lean_is_exclusive(v___x_6878_)) as u8;
                    if v_isSharedCheck_6900_ == 0 {
                        v___x_6895_ = v___x_6878_;
                        v_isShared_6896_ = v_isSharedCheck_6900_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6893_);
                        crate::leanh::lean_dec(v___x_6878_);
                        v___x_6895_ = crate::leanh::lean_box(0);
                        v_isShared_6896_ = v_isSharedCheck_6900_;
                        state = 19;
                        continue;
                    }
                }
            }
            16 => {
                v_decl_6831_ = v___x_6883_;
                state = 7;
                continue;
            }
            17 => {
                if v_isShared_6888_ == 0 {
                    v___x_6890_ = v___x_6887_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6891_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6891_, 0, v_a_6885_);
                    v___x_6890_ = v_reuseFailAlloc_6891_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_6890_;
            }
            19 => {
                if v_isShared_6896_ == 0 {
                    v___x_6898_ = v___x_6895_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_6899_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6899_, 0, v_a_6893_);
                    v___x_6898_ = v_reuseFailAlloc_6899_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_6898_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6___boxed(
    mut v_as_6909_: *mut crate::leanh::LeanObject,
    mut v_sz_6910_: *mut crate::leanh::LeanObject,
    mut v_i_6911_: *mut crate::leanh::LeanObject,
    mut v_b_6912_: *mut crate::leanh::LeanObject,
    mut v___y_6913_: *mut crate::leanh::LeanObject,
    mut v___y_6914_: *mut crate::leanh::LeanObject,
    mut v___y_6915_: *mut crate::leanh::LeanObject,
    mut v___y_6916_: *mut crate::leanh::LeanObject,
    mut v___y_6917_: *mut crate::leanh::LeanObject,
    mut v___y_6918_: *mut crate::leanh::LeanObject,
    mut v___y_6919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6920_: usize = 0;
    let mut v_i_boxed_6921_: usize = 0;
    let mut v_res_6922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6920_ = crate::leanh::lean_unbox_usize(v_sz_6910_);
    crate::leanh::lean_dec(v_sz_6910_);
    v_i_boxed_6921_ = crate::leanh::lean_unbox_usize(v_i_6911_);
    crate::leanh::lean_dec(v_i_6911_);
    v_res_6922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(v_as_6909_, v_sz_boxed_6920_, v_i_boxed_6921_, v_b_6912_, v___y_6913_, v___y_6914_, v___y_6915_, v___y_6916_, v___y_6917_, v___y_6918_);
    crate::leanh::lean_dec(v___y_6918_);
    crate::leanh::lean_dec_ref(v___y_6917_);
    crate::leanh::lean_dec(v___y_6916_);
    crate::leanh::lean_dec_ref(v___y_6915_);
    crate::leanh::lean_dec(v___y_6914_);
    crate::leanh::lean_dec_ref(v___y_6913_);
    crate::leanh::lean_dec_ref(v_as_6909_);
    return v_res_6922_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(
    mut v_init_6923_: *mut crate::leanh::LeanObject,
    mut v_n_6924_: *mut crate::leanh::LeanObject,
    mut v_b_6925_: *mut crate::leanh::LeanObject,
    mut v___y_6926_: *mut crate::leanh::LeanObject,
    mut v___y_6927_: *mut crate::leanh::LeanObject,
    mut v___y_6928_: *mut crate::leanh::LeanObject,
    mut v___y_6929_: *mut crate::leanh::LeanObject,
    mut v___y_6930_: *mut crate::leanh::LeanObject,
    mut v___y_6931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_6933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6936_: usize = 0;
    let mut v___x_6937_: usize = 0;
    let mut v___x_6938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6942_: u8 = 0;
    let mut v_fst_6943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6953_: u8 = 0;
    let mut v_a_6954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6957_: u8 = 0;
    let mut v___x_6959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6961_: u8 = 0;
    let mut v_vs_6962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6965_: usize = 0;
    let mut v___x_6966_: usize = 0;
    let mut v___x_6967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6971_: u8 = 0;
    let mut v_fst_6972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6982_: u8 = 0;
    let mut v_a_6983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6986_: u8 = 0;
    let mut v___x_6988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6990_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_6924_) == 0 {
                    v_cs_6933_ = crate::leanh::lean_ctor_get(v_n_6924_, 0);
                    v___x_6934_ = crate::leanh::lean_box(0);
                    v___x_6935_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6935_, 0, v___x_6934_);
                    crate::leanh::lean_ctor_set(v___x_6935_, 1, v_b_6925_);
                    v_sz_6936_ = lean_array_size(v_cs_6933_);
                    v___x_6937_ = 0usize;
                    v___x_6938_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(v_init_6923_, v_cs_6933_, v_sz_6936_, v___x_6937_, v___x_6935_, v___y_6926_, v___y_6927_, v___y_6928_, v___y_6929_, v___y_6930_, v___y_6931_);
                    if crate::leanh::lean_obj_tag(v___x_6938_) == 0 {
                        v_a_6939_ = crate::leanh::lean_ctor_get(v___x_6938_, 0);
                        v_isSharedCheck_6953_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6938_)) as u8;
                        if v_isSharedCheck_6953_ == 0 {
                            v___x_6941_ = v___x_6938_;
                            v_isShared_6942_ = v_isSharedCheck_6953_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6939_);
                            crate::leanh::lean_dec(v___x_6938_);
                            v___x_6941_ = crate::leanh::lean_box(0);
                            v_isShared_6942_ = v_isSharedCheck_6953_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6954_ = crate::leanh::lean_ctor_get(v___x_6938_, 0);
                        v_isSharedCheck_6961_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6938_)) as u8;
                        if v_isSharedCheck_6961_ == 0 {
                            v___x_6956_ = v___x_6938_;
                            v_isShared_6957_ = v_isSharedCheck_6961_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6954_);
                            crate::leanh::lean_dec(v___x_6938_);
                            v___x_6956_ = crate::leanh::lean_box(0);
                            v_isShared_6957_ = v_isSharedCheck_6961_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_6962_ = crate::leanh::lean_ctor_get(v_n_6924_, 0);
                    v___x_6963_ = crate::leanh::lean_box(0);
                    v___x_6964_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6964_, 0, v___x_6963_);
                    crate::leanh::lean_ctor_set(v___x_6964_, 1, v_b_6925_);
                    v_sz_6965_ = lean_array_size(v_vs_6962_);
                    v___x_6966_ = 0usize;
                    v___x_6967_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(v_vs_6962_, v_sz_6965_, v___x_6966_, v___x_6964_, v___y_6926_, v___y_6927_, v___y_6928_, v___y_6929_, v___y_6930_, v___y_6931_);
                    if crate::leanh::lean_obj_tag(v___x_6967_) == 0 {
                        v_a_6968_ = crate::leanh::lean_ctor_get(v___x_6967_, 0);
                        v_isSharedCheck_6982_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6967_)) as u8;
                        if v_isSharedCheck_6982_ == 0 {
                            v___x_6970_ = v___x_6967_;
                            v_isShared_6971_ = v_isSharedCheck_6982_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6968_);
                            crate::leanh::lean_dec(v___x_6967_);
                            v___x_6970_ = crate::leanh::lean_box(0);
                            v_isShared_6971_ = v_isSharedCheck_6982_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_6983_ = crate::leanh::lean_ctor_get(v___x_6967_, 0);
                        v_isSharedCheck_6990_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6967_)) as u8;
                        if v_isSharedCheck_6990_ == 0 {
                            v___x_6985_ = v___x_6967_;
                            v_isShared_6986_ = v_isSharedCheck_6990_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6983_);
                            crate::leanh::lean_dec(v___x_6967_);
                            v___x_6985_ = crate::leanh::lean_box(0);
                            v_isShared_6986_ = v_isSharedCheck_6990_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_6943_ = crate::leanh::lean_ctor_get(v_a_6939_, 0);
                if crate::leanh::lean_obj_tag(v_fst_6943_) == 0 {
                    v_snd_6944_ = crate::leanh::lean_ctor_get(v_a_6939_, 1);
                    crate::leanh::lean_inc(v_snd_6944_);
                    crate::leanh::lean_dec(v_a_6939_);
                    v___x_6945_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6945_, 0, v_snd_6944_);
                    if v_isShared_6942_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6941_, 0, v___x_6945_);
                        v___x_6947_ = v___x_6941_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6948_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6948_, 0, v___x_6945_);
                        v___x_6947_ = v_reuseFailAlloc_6948_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_6943_);
                    crate::leanh::lean_dec(v_a_6939_);
                    v_val_6949_ = crate::leanh::lean_ctor_get(v_fst_6943_, 0);
                    crate::leanh::lean_inc(v_val_6949_);
                    crate::leanh::lean_dec_ref_known(v_fst_6943_, 1);
                    if v_isShared_6942_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6941_, 0, v_val_6949_);
                        v___x_6951_ = v___x_6941_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6952_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6952_, 0, v_val_6949_);
                        v___x_6951_ = v_reuseFailAlloc_6952_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6947_;
            }
            3 => {
                return v___x_6951_;
            }
            4 => {
                if v_isShared_6957_ == 0 {
                    v___x_6959_ = v___x_6956_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6960_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6960_, 0, v_a_6954_);
                    v___x_6959_ = v_reuseFailAlloc_6960_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6959_;
            }
            6 => {
                v_fst_6972_ = crate::leanh::lean_ctor_get(v_a_6968_, 0);
                if crate::leanh::lean_obj_tag(v_fst_6972_) == 0 {
                    v_snd_6973_ = crate::leanh::lean_ctor_get(v_a_6968_, 1);
                    crate::leanh::lean_inc(v_snd_6973_);
                    crate::leanh::lean_dec(v_a_6968_);
                    v___x_6974_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6974_, 0, v_snd_6973_);
                    if v_isShared_6971_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6970_, 0, v___x_6974_);
                        v___x_6976_ = v___x_6970_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6977_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6977_, 0, v___x_6974_);
                        v___x_6976_ = v_reuseFailAlloc_6977_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_6972_);
                    crate::leanh::lean_dec(v_a_6968_);
                    v_val_6978_ = crate::leanh::lean_ctor_get(v_fst_6972_, 0);
                    crate::leanh::lean_inc(v_val_6978_);
                    crate::leanh::lean_dec_ref_known(v_fst_6972_, 1);
                    if v_isShared_6971_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6970_, 0, v_val_6978_);
                        v___x_6980_ = v___x_6970_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6981_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6981_, 0, v_val_6978_);
                        v___x_6980_ = v_reuseFailAlloc_6981_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_6976_;
            }
            8 => {
                return v___x_6980_;
            }
            9 => {
                if v_isShared_6986_ == 0 {
                    v___x_6988_ = v___x_6985_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6989_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6989_, 0, v_a_6983_);
                    v___x_6988_ = v_reuseFailAlloc_6989_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6988_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(
    mut v_init_6991_: *mut crate::leanh::LeanObject,
    mut v_as_6992_: *mut crate::leanh::LeanObject,
    mut v_sz_6993_: usize,
    mut v_i_6994_: usize,
    mut v_b_6995_: *mut crate::leanh::LeanObject,
    mut v___y_6996_: *mut crate::leanh::LeanObject,
    mut v___y_6997_: *mut crate::leanh::LeanObject,
    mut v___y_6998_: *mut crate::leanh::LeanObject,
    mut v___y_6999_: *mut crate::leanh::LeanObject,
    mut v___y_7000_: *mut crate::leanh::LeanObject,
    mut v___y_7001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7003_: u8 = 0;
    let mut v___x_7004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7008_: u8 = 0;
    let mut v_a_7009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7014_: u8 = 0;
    let mut v___x_7015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7026_: usize = 0;
    let mut v___x_7027_: usize = 0;
    let mut v_reuseFailAlloc_7029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7030_: u8 = 0;
    let mut v_a_7031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7034_: u8 = 0;
    let mut v___x_7036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7038_: u8 = 0;
    let mut v_isSharedCheck_7039_: u8 = 0;
    let mut v_unused_7040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7003_ = lean_usize_dec_lt(v_i_6994_, v_sz_6993_);
                if v___x_7003_ == 0 {
                    v___x_7004_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7004_, 0, v_b_6995_);
                    return v___x_7004_;
                } else {
                    v_snd_7005_ = crate::leanh::lean_ctor_get(v_b_6995_, 1);
                    v_isSharedCheck_7039_ = (!crate::leanh::lean_is_exclusive(v_b_6995_)) as u8;
                    if v_isSharedCheck_7039_ == 0 {
                        v_unused_7040_ = crate::leanh::lean_ctor_get(v_b_6995_, 0);
                        crate::leanh::lean_dec(v_unused_7040_);
                        v___x_7007_ = v_b_6995_;
                        v_isShared_7008_ = v_isSharedCheck_7039_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_7005_);
                        crate::leanh::lean_dec(v_b_6995_);
                        v___x_7007_ = crate::leanh::lean_box(0);
                        v_isShared_7008_ = v_isSharedCheck_7039_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_7009_ = lean_array_uget_borrowed(v_as_6992_, v_i_6994_);
                crate::leanh::lean_inc(v_snd_7005_);
                v___x_7010_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_init_6991_, v_a_7009_, v_snd_7005_, v___y_6996_, v___y_6997_, v___y_6998_, v___y_6999_, v___y_7000_, v___y_7001_);
                if crate::leanh::lean_obj_tag(v___x_7010_) == 0 {
                    v_a_7011_ = crate::leanh::lean_ctor_get(v___x_7010_, 0);
                    v_isSharedCheck_7030_ = (!crate::leanh::lean_is_exclusive(v___x_7010_)) as u8;
                    if v_isSharedCheck_7030_ == 0 {
                        v___x_7013_ = v___x_7010_;
                        v_isShared_7014_ = v_isSharedCheck_7030_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7011_);
                        crate::leanh::lean_dec(v___x_7010_);
                        v___x_7013_ = crate::leanh::lean_box(0);
                        v_isShared_7014_ = v_isSharedCheck_7030_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7007_);
                    crate::leanh::lean_dec(v_snd_7005_);
                    v_a_7031_ = crate::leanh::lean_ctor_get(v___x_7010_, 0);
                    v_isSharedCheck_7038_ = (!crate::leanh::lean_is_exclusive(v___x_7010_)) as u8;
                    if v_isSharedCheck_7038_ == 0 {
                        v___x_7033_ = v___x_7010_;
                        v_isShared_7034_ = v_isSharedCheck_7038_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7031_);
                        crate::leanh::lean_dec(v___x_7010_);
                        v___x_7033_ = crate::leanh::lean_box(0);
                        v_isShared_7034_ = v_isSharedCheck_7038_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_7011_) == 0 {
                    v___x_7015_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7015_, 0, v_a_7011_);
                    if v_isShared_7008_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7007_, 0, v___x_7015_);
                        v___x_7017_ = v___x_7007_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7021_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7021_, 0, v___x_7015_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7021_, 1, v_snd_7005_);
                        v___x_7017_ = v_reuseFailAlloc_7021_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7013_);
                    crate::leanh::lean_dec(v_snd_7005_);
                    v_a_7022_ = crate::leanh::lean_ctor_get(v_a_7011_, 0);
                    crate::leanh::lean_inc(v_a_7022_);
                    crate::leanh::lean_dec_ref_known(v_a_7011_, 1);
                    v___x_7023_ = crate::leanh::lean_box(0);
                    if v_isShared_7008_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7007_, 1, v_a_7022_);
                        crate::leanh::lean_ctor_set(v___x_7007_, 0, v___x_7023_);
                        v___x_7025_ = v___x_7007_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_7029_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7029_, 0, v___x_7023_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7029_, 1, v_a_7022_);
                        v___x_7025_ = v_reuseFailAlloc_7029_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_7014_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7013_, 0, v___x_7017_);
                    v___x_7019_ = v___x_7013_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7020_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7020_, 0, v___x_7017_);
                    v___x_7019_ = v_reuseFailAlloc_7020_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7019_;
            }
            5 => {
                v___x_7026_ = 1usize;
                v___x_7027_ = lean_usize_add(v_i_6994_, v___x_7026_);
                v_i_6994_ = v___x_7027_;
                v_b_6995_ = v___x_7025_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_7034_ == 0 {
                    v___x_7036_ = v___x_7033_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7037_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7037_, 0, v_a_7031_);
                    v___x_7036_ = v_reuseFailAlloc_7037_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7036_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5___boxed(
    mut v_init_7041_: *mut crate::leanh::LeanObject,
    mut v_as_7042_: *mut crate::leanh::LeanObject,
    mut v_sz_7043_: *mut crate::leanh::LeanObject,
    mut v_i_7044_: *mut crate::leanh::LeanObject,
    mut v_b_7045_: *mut crate::leanh::LeanObject,
    mut v___y_7046_: *mut crate::leanh::LeanObject,
    mut v___y_7047_: *mut crate::leanh::LeanObject,
    mut v___y_7048_: *mut crate::leanh::LeanObject,
    mut v___y_7049_: *mut crate::leanh::LeanObject,
    mut v___y_7050_: *mut crate::leanh::LeanObject,
    mut v___y_7051_: *mut crate::leanh::LeanObject,
    mut v___y_7052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_7053_: usize = 0;
    let mut v_i_boxed_7054_: usize = 0;
    let mut v_res_7055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7053_ = crate::leanh::lean_unbox_usize(v_sz_7043_);
    crate::leanh::lean_dec(v_sz_7043_);
    v_i_boxed_7054_ = crate::leanh::lean_unbox_usize(v_i_7044_);
    crate::leanh::lean_dec(v_i_7044_);
    v_res_7055_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(v_init_7041_, v_as_7042_, v_sz_boxed_7053_, v_i_boxed_7054_, v_b_7045_, v___y_7046_, v___y_7047_, v___y_7048_, v___y_7049_, v___y_7050_, v___y_7051_);
    crate::leanh::lean_dec(v___y_7051_);
    crate::leanh::lean_dec_ref(v___y_7050_);
    crate::leanh::lean_dec(v___y_7049_);
    crate::leanh::lean_dec_ref(v___y_7048_);
    crate::leanh::lean_dec(v___y_7047_);
    crate::leanh::lean_dec_ref(v___y_7046_);
    crate::leanh::lean_dec_ref(v_as_7042_);
    crate::leanh::lean_dec_ref(v_init_7041_);
    return v_res_7055_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2___boxed(
    mut v_init_7056_: *mut crate::leanh::LeanObject,
    mut v_n_7057_: *mut crate::leanh::LeanObject,
    mut v_b_7058_: *mut crate::leanh::LeanObject,
    mut v___y_7059_: *mut crate::leanh::LeanObject,
    mut v___y_7060_: *mut crate::leanh::LeanObject,
    mut v___y_7061_: *mut crate::leanh::LeanObject,
    mut v___y_7062_: *mut crate::leanh::LeanObject,
    mut v___y_7063_: *mut crate::leanh::LeanObject,
    mut v___y_7064_: *mut crate::leanh::LeanObject,
    mut v___y_7065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7066_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_init_7056_, v_n_7057_, v_b_7058_, v___y_7059_, v___y_7060_, v___y_7061_, v___y_7062_, v___y_7063_, v___y_7064_);
    crate::leanh::lean_dec(v___y_7064_);
    crate::leanh::lean_dec_ref(v___y_7063_);
    crate::leanh::lean_dec(v___y_7062_);
    crate::leanh::lean_dec_ref(v___y_7061_);
    crate::leanh::lean_dec(v___y_7060_);
    crate::leanh::lean_dec_ref(v___y_7059_);
    crate::leanh::lean_dec_ref(v_n_7057_);
    crate::leanh::lean_dec_ref(v_init_7056_);
    return v_res_7066_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(
    mut v_as_7067_: *mut crate::leanh::LeanObject,
    mut v_sz_7068_: usize,
    mut v_i_7069_: usize,
    mut v_b_7070_: *mut crate::leanh::LeanObject,
    mut v___y_7071_: *mut crate::leanh::LeanObject,
    mut v___y_7072_: *mut crate::leanh::LeanObject,
    mut v___y_7073_: *mut crate::leanh::LeanObject,
    mut v___y_7074_: *mut crate::leanh::LeanObject,
    mut v___y_7075_: *mut crate::leanh::LeanObject,
    mut v___y_7076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7078_: u8 = 0;
    let mut v___x_7079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7083_: u8 = 0;
    let mut v___x_7084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7089_: usize = 0;
    let mut v___x_7090_: usize = 0;
    let mut v_reuseFailAlloc_7092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7098_: u8 = 0;
    let mut v_fst_7099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7102_: u8 = 0;
    let mut v_fst_7103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7107_: u8 = 0;
    let mut v_decl_7109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_7125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bi_7127_: u8 = 0;
    let mut v_kind_7128_: u8 = 0;
    let mut v___x_7130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7131_: u8 = 0;
    let mut v___x_7132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7140_: u8 = 0;
    let mut v___x_7142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7144_: u8 = 0;
    let mut v_isSharedCheck_7145_: u8 = 0;
    let mut v_unused_7146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_7148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_7151_: u8 = 0;
    let mut v_kind_7152_: u8 = 0;
    let mut v___x_7154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7155_: u8 = 0;
    let mut v___x_7156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7166_: u8 = 0;
    let mut v___x_7168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7170_: u8 = 0;
    let mut v_a_7171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7174_: u8 = 0;
    let mut v___x_7176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7178_: u8 = 0;
    let mut v_isSharedCheck_7179_: u8 = 0;
    let mut v_unused_7180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7181_: u8 = 0;
    let mut v_isSharedCheck_7182_: u8 = 0;
    let mut v_unused_7183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7184_: u8 = 0;
    let mut v_isSharedCheck_7185_: u8 = 0;
    let mut v_unused_7186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7078_ = lean_usize_dec_lt(v_i_7069_, v_sz_7068_);
                if v___x_7078_ == 0 {
                    v___x_7079_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7079_, 0, v_b_7070_);
                    return v___x_7079_;
                } else {
                    v_snd_7080_ = crate::leanh::lean_ctor_get(v_b_7070_, 1);
                    v_isSharedCheck_7185_ = (!crate::leanh::lean_is_exclusive(v_b_7070_)) as u8;
                    if v_isSharedCheck_7185_ == 0 {
                        v_unused_7186_ = crate::leanh::lean_ctor_get(v_b_7070_, 0);
                        crate::leanh::lean_dec(v_unused_7186_);
                        v___x_7082_ = v_b_7070_;
                        v_isShared_7083_ = v_isSharedCheck_7185_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_7080_);
                        crate::leanh::lean_dec(v_b_7070_);
                        v___x_7082_ = crate::leanh::lean_box(0);
                        v_isShared_7083_ = v_isSharedCheck_7185_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7084_ = crate::leanh::lean_box(0);
                v_a_7093_ = lean_array_uget(v_as_7067_, v_i_7069_);
                if crate::leanh::lean_obj_tag(v_a_7093_) == 0 {
                    v_a_7086_ = v_snd_7080_;
                    state = 2;
                    continue;
                } else {
                    v_snd_7094_ = crate::leanh::lean_ctor_get(v_snd_7080_, 1);
                    crate::leanh::lean_inc(v_snd_7094_);
                    v_val_7095_ = crate::leanh::lean_ctor_get(v_a_7093_, 0);
                    v_isSharedCheck_7184_ = (!crate::leanh::lean_is_exclusive(v_a_7093_)) as u8;
                    if v_isSharedCheck_7184_ == 0 {
                        v___x_7097_ = v_a_7093_;
                        v_isShared_7098_ = v_isSharedCheck_7184_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_7095_);
                        crate::leanh::lean_dec(v_a_7093_);
                        v___x_7097_ = crate::leanh::lean_box(0);
                        v_isShared_7098_ = v_isSharedCheck_7184_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7083_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7082_, 1, v_a_7086_);
                    crate::leanh::lean_ctor_set(v___x_7082_, 0, v___x_7084_);
                    v___x_7088_ = v___x_7082_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7092_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7092_, 0, v___x_7084_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7092_, 1, v_a_7086_);
                    v___x_7088_ = v_reuseFailAlloc_7092_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7089_ = 1usize;
                v___x_7090_ = lean_usize_add(v_i_7069_, v___x_7089_);
                v_i_7069_ = v___x_7090_;
                v_b_7070_ = v___x_7088_;
                state = 0;
                continue;
            }
            4 => {
                v_fst_7099_ = crate::leanh::lean_ctor_get(v_snd_7080_, 0);
                v_isSharedCheck_7182_ = (!crate::leanh::lean_is_exclusive(v_snd_7080_)) as u8;
                if v_isSharedCheck_7182_ == 0 {
                    v_unused_7183_ = crate::leanh::lean_ctor_get(v_snd_7080_, 1);
                    crate::leanh::lean_dec(v_unused_7183_);
                    v___x_7101_ = v_snd_7080_;
                    v_isShared_7102_ = v_isSharedCheck_7182_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_7099_);
                    crate::leanh::lean_dec(v_snd_7080_);
                    v___x_7101_ = crate::leanh::lean_box(0);
                    v_isShared_7102_ = v_isSharedCheck_7182_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_fst_7103_ = crate::leanh::lean_ctor_get(v_snd_7094_, 0);
                v_snd_7104_ = crate::leanh::lean_ctor_get(v_snd_7094_, 1);
                v_isSharedCheck_7181_ = (!crate::leanh::lean_is_exclusive(v_snd_7094_)) as u8;
                if v_isSharedCheck_7181_ == 0 {
                    v___x_7106_ = v_snd_7094_;
                    v_isShared_7107_ = v_isSharedCheck_7181_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_7104_);
                    crate::leanh::lean_inc(v_fst_7103_);
                    crate::leanh::lean_dec(v_snd_7094_);
                    v___x_7106_ = crate::leanh::lean_box(0);
                    v_isShared_7107_ = v_isSharedCheck_7181_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if crate::leanh::lean_obj_tag(v_val_7095_) == 0 {
                    v_fvarId_7124_ = crate::leanh::lean_ctor_get(v_val_7095_, 1);
                    v_userName_7125_ = crate::leanh::lean_ctor_get(v_val_7095_, 2);
                    v_type_7126_ = crate::leanh::lean_ctor_get(v_val_7095_, 3);
                    v_bi_7127_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_7095_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    v_kind_7128_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_7095_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                    );
                    v_isSharedCheck_7145_ = (!crate::leanh::lean_is_exclusive(v_val_7095_)) as u8;
                    if v_isSharedCheck_7145_ == 0 {
                        v_unused_7146_ = crate::leanh::lean_ctor_get(v_val_7095_, 0);
                        crate::leanh::lean_dec(v_unused_7146_);
                        v___x_7130_ = v_val_7095_;
                        v_isShared_7131_ = v_isSharedCheck_7145_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_type_7126_);
                        crate::leanh::lean_inc(v_userName_7125_);
                        crate::leanh::lean_inc(v_fvarId_7124_);
                        crate::leanh::lean_dec(v_val_7095_);
                        v___x_7130_ = crate::leanh::lean_box(0);
                        v_isShared_7131_ = v_isSharedCheck_7145_;
                        state = 11;
                        continue;
                    }
                } else {
                    v_fvarId_7147_ = crate::leanh::lean_ctor_get(v_val_7095_, 1);
                    v_userName_7148_ = crate::leanh::lean_ctor_get(v_val_7095_, 2);
                    v_type_7149_ = crate::leanh::lean_ctor_get(v_val_7095_, 3);
                    v_value_7150_ = crate::leanh::lean_ctor_get(v_val_7095_, 4);
                    v_nondep_7151_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_7095_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    );
                    v_kind_7152_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_7095_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    );
                    v_isSharedCheck_7179_ = (!crate::leanh::lean_is_exclusive(v_val_7095_)) as u8;
                    if v_isSharedCheck_7179_ == 0 {
                        v_unused_7180_ = crate::leanh::lean_ctor_get(v_val_7095_, 0);
                        crate::leanh::lean_dec(v_unused_7180_);
                        v___x_7154_ = v_val_7095_;
                        v_isShared_7155_ = v_isSharedCheck_7179_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_7150_);
                        crate::leanh::lean_inc(v_type_7149_);
                        crate::leanh::lean_inc(v_userName_7148_);
                        crate::leanh::lean_inc(v_fvarId_7147_);
                        crate::leanh::lean_dec(v_val_7095_);
                        v___x_7154_ = crate::leanh::lean_box(0);
                        v_isShared_7155_ = v_isSharedCheck_7179_;
                        state = 15;
                        continue;
                    }
                }
            }
            7 => {
                v___x_7110_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_7111_ = lean_nat_add(v_snd_7104_, v___x_7110_);
                crate::leanh::lean_dec(v_snd_7104_);
                crate::leanh::lean_inc_ref(v_decl_7109_);
                if v_isShared_7098_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7097_, 0, v_decl_7109_);
                    v___x_7113_ = v___x_7097_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7123_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7123_, 0, v_decl_7109_);
                    v___x_7113_ = v_reuseFailAlloc_7123_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_7114_ = l_Lean_PersistentArray_push___redArg(v_fst_7103_, v___x_7113_);
                v___x_7115_ = l_Lean_LocalDecl_fvarId(v_decl_7109_);
                v___x_7116_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_7099_, v___x_7115_, v_decl_7109_);
                if v_isShared_7107_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7106_, 1, v___x_7111_);
                    crate::leanh::lean_ctor_set(v___x_7106_, 0, v___x_7114_);
                    v___x_7118_ = v___x_7106_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7122_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7122_, 0, v___x_7114_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7122_, 1, v___x_7111_);
                    v___x_7118_ = v_reuseFailAlloc_7122_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_7102_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7101_, 1, v___x_7118_);
                    crate::leanh::lean_ctor_set(v___x_7101_, 0, v___x_7116_);
                    v___x_7120_ = v___x_7101_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7121_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7121_, 0, v___x_7116_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7121_, 1, v___x_7118_);
                    v___x_7120_ = v_reuseFailAlloc_7121_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_a_7086_ = v___x_7120_;
                state = 2;
                continue;
            }
            11 => {
                v___x_7132_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(
                    v_type_7126_,
                    v___y_7071_,
                    v___y_7072_,
                    v___y_7073_,
                    v___y_7074_,
                    v___y_7075_,
                    v___y_7076_,
                );
                if crate::leanh::lean_obj_tag(v___x_7132_) == 0 {
                    v_a_7133_ = crate::leanh::lean_ctor_get(v___x_7132_, 0);
                    crate::leanh::lean_inc(v_a_7133_);
                    crate::leanh::lean_dec_ref_known(v___x_7132_, 1);
                    crate::leanh::lean_inc(v_snd_7104_);
                    if v_isShared_7131_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7130_, 3, v_a_7133_);
                        crate::leanh::lean_ctor_set(v___x_7130_, 0, v_snd_7104_);
                        v___x_7135_ = v___x_7130_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_7136_ = crate::leanh::lean_alloc_ctor(0, 4, (2) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7136_, 0, v_snd_7104_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7136_, 1, v_fvarId_7124_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7136_, 2, v_userName_7125_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7136_, 3, v_a_7133_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_7136_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            v_bi_7127_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_7136_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                            v_kind_7128_,
                        );
                        v___x_7135_ = v_reuseFailAlloc_7136_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7130_);
                    crate::leanh::lean_dec(v_userName_7125_);
                    crate::leanh::lean_dec(v_fvarId_7124_);
                    crate::leanh::lean_del_object(v___x_7106_);
                    crate::leanh::lean_dec(v_snd_7104_);
                    crate::leanh::lean_dec(v_fst_7103_);
                    crate::leanh::lean_del_object(v___x_7101_);
                    crate::leanh::lean_dec(v_fst_7099_);
                    crate::leanh::lean_del_object(v___x_7097_);
                    crate::leanh::lean_del_object(v___x_7082_);
                    v_a_7137_ = crate::leanh::lean_ctor_get(v___x_7132_, 0);
                    v_isSharedCheck_7144_ = (!crate::leanh::lean_is_exclusive(v___x_7132_)) as u8;
                    if v_isSharedCheck_7144_ == 0 {
                        v___x_7139_ = v___x_7132_;
                        v_isShared_7140_ = v_isSharedCheck_7144_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7137_);
                        crate::leanh::lean_dec(v___x_7132_);
                        v___x_7139_ = crate::leanh::lean_box(0);
                        v_isShared_7140_ = v_isSharedCheck_7144_;
                        state = 13;
                        continue;
                    }
                }
            }
            12 => {
                v_decl_7109_ = v___x_7135_;
                state = 7;
                continue;
            }
            13 => {
                if v_isShared_7140_ == 0 {
                    v___x_7142_ = v___x_7139_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_7143_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7143_, 0, v_a_7137_);
                    v___x_7142_ = v_reuseFailAlloc_7143_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_7142_;
            }
            15 => {
                v___x_7156_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(
                    v_type_7149_,
                    v___y_7071_,
                    v___y_7072_,
                    v___y_7073_,
                    v___y_7074_,
                    v___y_7075_,
                    v___y_7076_,
                );
                if crate::leanh::lean_obj_tag(v___x_7156_) == 0 {
                    v_a_7157_ = crate::leanh::lean_ctor_get(v___x_7156_, 0);
                    crate::leanh::lean_inc(v_a_7157_);
                    crate::leanh::lean_dec_ref_known(v___x_7156_, 1);
                    v___x_7158_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(
                        v_value_7150_,
                        v___y_7071_,
                        v___y_7072_,
                        v___y_7073_,
                        v___y_7074_,
                        v___y_7075_,
                        v___y_7076_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7158_) == 0 {
                        v_a_7159_ = crate::leanh::lean_ctor_get(v___x_7158_, 0);
                        crate::leanh::lean_inc(v_a_7159_);
                        crate::leanh::lean_dec_ref_known(v___x_7158_, 1);
                        crate::leanh::lean_inc(v_snd_7104_);
                        if v_isShared_7155_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_7154_, 4, v_a_7159_);
                            crate::leanh::lean_ctor_set(v___x_7154_, 3, v_a_7157_);
                            crate::leanh::lean_ctor_set(v___x_7154_, 0, v_snd_7104_);
                            v___x_7161_ = v___x_7154_;
                            state = 16;
                            continue;
                        } else {
                            v_reuseFailAlloc_7162_ =
                                crate::leanh::lean_alloc_ctor(1, 5, (2) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7162_, 0, v_snd_7104_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7162_, 1, v_fvarId_7147_);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_7162_,
                                2,
                                v_userName_7148_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7162_, 3, v_a_7157_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7162_, 4, v_a_7159_);
                            crate::leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_7162_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                                v_nondep_7151_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_7162_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1)
                                    as u32,
                                v_kind_7152_,
                            );
                            v___x_7161_ = v_reuseFailAlloc_7162_;
                            state = 16;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_7157_);
                        crate::leanh::lean_del_object(v___x_7154_);
                        crate::leanh::lean_dec(v_userName_7148_);
                        crate::leanh::lean_dec(v_fvarId_7147_);
                        crate::leanh::lean_del_object(v___x_7106_);
                        crate::leanh::lean_dec(v_snd_7104_);
                        crate::leanh::lean_dec(v_fst_7103_);
                        crate::leanh::lean_del_object(v___x_7101_);
                        crate::leanh::lean_dec(v_fst_7099_);
                        crate::leanh::lean_del_object(v___x_7097_);
                        crate::leanh::lean_del_object(v___x_7082_);
                        v_a_7163_ = crate::leanh::lean_ctor_get(v___x_7158_, 0);
                        v_isSharedCheck_7170_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7158_)) as u8;
                        if v_isSharedCheck_7170_ == 0 {
                            v___x_7165_ = v___x_7158_;
                            v_isShared_7166_ = v_isSharedCheck_7170_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7163_);
                            crate::leanh::lean_dec(v___x_7158_);
                            v___x_7165_ = crate::leanh::lean_box(0);
                            v_isShared_7166_ = v_isSharedCheck_7170_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7154_);
                    crate::leanh::lean_dec_ref(v_value_7150_);
                    crate::leanh::lean_dec(v_userName_7148_);
                    crate::leanh::lean_dec(v_fvarId_7147_);
                    crate::leanh::lean_del_object(v___x_7106_);
                    crate::leanh::lean_dec(v_snd_7104_);
                    crate::leanh::lean_dec(v_fst_7103_);
                    crate::leanh::lean_del_object(v___x_7101_);
                    crate::leanh::lean_dec(v_fst_7099_);
                    crate::leanh::lean_del_object(v___x_7097_);
                    crate::leanh::lean_del_object(v___x_7082_);
                    v_a_7171_ = crate::leanh::lean_ctor_get(v___x_7156_, 0);
                    v_isSharedCheck_7178_ = (!crate::leanh::lean_is_exclusive(v___x_7156_)) as u8;
                    if v_isSharedCheck_7178_ == 0 {
                        v___x_7173_ = v___x_7156_;
                        v_isShared_7174_ = v_isSharedCheck_7178_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7171_);
                        crate::leanh::lean_dec(v___x_7156_);
                        v___x_7173_ = crate::leanh::lean_box(0);
                        v_isShared_7174_ = v_isSharedCheck_7178_;
                        state = 19;
                        continue;
                    }
                }
            }
            16 => {
                v_decl_7109_ = v___x_7161_;
                state = 7;
                continue;
            }
            17 => {
                if v_isShared_7166_ == 0 {
                    v___x_7168_ = v___x_7165_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_7169_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7169_, 0, v_a_7163_);
                    v___x_7168_ = v_reuseFailAlloc_7169_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_7168_;
            }
            19 => {
                if v_isShared_7174_ == 0 {
                    v___x_7176_ = v___x_7173_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_7177_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7177_, 0, v_a_7171_);
                    v___x_7176_ = v_reuseFailAlloc_7177_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_7176_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8___boxed(
    mut v_as_7187_: *mut crate::leanh::LeanObject,
    mut v_sz_7188_: *mut crate::leanh::LeanObject,
    mut v_i_7189_: *mut crate::leanh::LeanObject,
    mut v_b_7190_: *mut crate::leanh::LeanObject,
    mut v___y_7191_: *mut crate::leanh::LeanObject,
    mut v___y_7192_: *mut crate::leanh::LeanObject,
    mut v___y_7193_: *mut crate::leanh::LeanObject,
    mut v___y_7194_: *mut crate::leanh::LeanObject,
    mut v___y_7195_: *mut crate::leanh::LeanObject,
    mut v___y_7196_: *mut crate::leanh::LeanObject,
    mut v___y_7197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_7198_: usize = 0;
    let mut v_i_boxed_7199_: usize = 0;
    let mut v_res_7200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7198_ = crate::leanh::lean_unbox_usize(v_sz_7188_);
    crate::leanh::lean_dec(v_sz_7188_);
    v_i_boxed_7199_ = crate::leanh::lean_unbox_usize(v_i_7189_);
    crate::leanh::lean_dec(v_i_7189_);
    v_res_7200_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(v_as_7187_, v_sz_boxed_7198_, v_i_boxed_7199_, v_b_7190_, v___y_7191_, v___y_7192_, v___y_7193_, v___y_7194_, v___y_7195_, v___y_7196_);
    crate::leanh::lean_dec(v___y_7196_);
    crate::leanh::lean_dec_ref(v___y_7195_);
    crate::leanh::lean_dec(v___y_7194_);
    crate::leanh::lean_dec_ref(v___y_7193_);
    crate::leanh::lean_dec(v___y_7192_);
    crate::leanh::lean_dec_ref(v___y_7191_);
    crate::leanh::lean_dec_ref(v_as_7187_);
    return v_res_7200_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(
    mut v_as_7201_: *mut crate::leanh::LeanObject,
    mut v_sz_7202_: usize,
    mut v_i_7203_: usize,
    mut v_b_7204_: *mut crate::leanh::LeanObject,
    mut v___y_7205_: *mut crate::leanh::LeanObject,
    mut v___y_7206_: *mut crate::leanh::LeanObject,
    mut v___y_7207_: *mut crate::leanh::LeanObject,
    mut v___y_7208_: *mut crate::leanh::LeanObject,
    mut v___y_7209_: *mut crate::leanh::LeanObject,
    mut v___y_7210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7212_: u8 = 0;
    let mut v___x_7213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7217_: u8 = 0;
    let mut v___x_7218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7223_: usize = 0;
    let mut v___x_7224_: usize = 0;
    let mut v___x_7225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7232_: u8 = 0;
    let mut v_fst_7233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7236_: u8 = 0;
    let mut v_fst_7237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7241_: u8 = 0;
    let mut v_decl_7243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_7259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bi_7261_: u8 = 0;
    let mut v_kind_7262_: u8 = 0;
    let mut v___x_7264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7265_: u8 = 0;
    let mut v___x_7266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7274_: u8 = 0;
    let mut v___x_7276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7278_: u8 = 0;
    let mut v_isSharedCheck_7279_: u8 = 0;
    let mut v_unused_7280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_7282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_7285_: u8 = 0;
    let mut v_kind_7286_: u8 = 0;
    let mut v___x_7288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7289_: u8 = 0;
    let mut v___x_7290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7300_: u8 = 0;
    let mut v___x_7302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7304_: u8 = 0;
    let mut v_a_7305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7308_: u8 = 0;
    let mut v___x_7310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7312_: u8 = 0;
    let mut v_isSharedCheck_7313_: u8 = 0;
    let mut v_unused_7314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7315_: u8 = 0;
    let mut v_isSharedCheck_7316_: u8 = 0;
    let mut v_unused_7317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7318_: u8 = 0;
    let mut v_isSharedCheck_7319_: u8 = 0;
    let mut v_unused_7320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7212_ = lean_usize_dec_lt(v_i_7203_, v_sz_7202_);
                if v___x_7212_ == 0 {
                    v___x_7213_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7213_, 0, v_b_7204_);
                    return v___x_7213_;
                } else {
                    v_snd_7214_ = crate::leanh::lean_ctor_get(v_b_7204_, 1);
                    v_isSharedCheck_7319_ = (!crate::leanh::lean_is_exclusive(v_b_7204_)) as u8;
                    if v_isSharedCheck_7319_ == 0 {
                        v_unused_7320_ = crate::leanh::lean_ctor_get(v_b_7204_, 0);
                        crate::leanh::lean_dec(v_unused_7320_);
                        v___x_7216_ = v_b_7204_;
                        v_isShared_7217_ = v_isSharedCheck_7319_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_7214_);
                        crate::leanh::lean_dec(v_b_7204_);
                        v___x_7216_ = crate::leanh::lean_box(0);
                        v_isShared_7217_ = v_isSharedCheck_7319_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7218_ = crate::leanh::lean_box(0);
                v_a_7227_ = lean_array_uget(v_as_7201_, v_i_7203_);
                if crate::leanh::lean_obj_tag(v_a_7227_) == 0 {
                    v_a_7220_ = v_snd_7214_;
                    state = 2;
                    continue;
                } else {
                    v_snd_7228_ = crate::leanh::lean_ctor_get(v_snd_7214_, 1);
                    crate::leanh::lean_inc(v_snd_7228_);
                    v_val_7229_ = crate::leanh::lean_ctor_get(v_a_7227_, 0);
                    v_isSharedCheck_7318_ = (!crate::leanh::lean_is_exclusive(v_a_7227_)) as u8;
                    if v_isSharedCheck_7318_ == 0 {
                        v___x_7231_ = v_a_7227_;
                        v_isShared_7232_ = v_isSharedCheck_7318_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_7229_);
                        crate::leanh::lean_dec(v_a_7227_);
                        v___x_7231_ = crate::leanh::lean_box(0);
                        v_isShared_7232_ = v_isSharedCheck_7318_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7217_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7216_, 1, v_a_7220_);
                    crate::leanh::lean_ctor_set(v___x_7216_, 0, v___x_7218_);
                    v___x_7222_ = v___x_7216_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7226_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7226_, 0, v___x_7218_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7226_, 1, v_a_7220_);
                    v___x_7222_ = v_reuseFailAlloc_7226_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7223_ = 1usize;
                v___x_7224_ = lean_usize_add(v_i_7203_, v___x_7223_);
                v___x_7225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(v_as_7201_, v_sz_7202_, v___x_7224_, v___x_7222_, v___y_7205_, v___y_7206_, v___y_7207_, v___y_7208_, v___y_7209_, v___y_7210_);
                return v___x_7225_;
            }
            4 => {
                v_fst_7233_ = crate::leanh::lean_ctor_get(v_snd_7214_, 0);
                v_isSharedCheck_7316_ = (!crate::leanh::lean_is_exclusive(v_snd_7214_)) as u8;
                if v_isSharedCheck_7316_ == 0 {
                    v_unused_7317_ = crate::leanh::lean_ctor_get(v_snd_7214_, 1);
                    crate::leanh::lean_dec(v_unused_7317_);
                    v___x_7235_ = v_snd_7214_;
                    v_isShared_7236_ = v_isSharedCheck_7316_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_7233_);
                    crate::leanh::lean_dec(v_snd_7214_);
                    v___x_7235_ = crate::leanh::lean_box(0);
                    v_isShared_7236_ = v_isSharedCheck_7316_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_fst_7237_ = crate::leanh::lean_ctor_get(v_snd_7228_, 0);
                v_snd_7238_ = crate::leanh::lean_ctor_get(v_snd_7228_, 1);
                v_isSharedCheck_7315_ = (!crate::leanh::lean_is_exclusive(v_snd_7228_)) as u8;
                if v_isSharedCheck_7315_ == 0 {
                    v___x_7240_ = v_snd_7228_;
                    v_isShared_7241_ = v_isSharedCheck_7315_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_7238_);
                    crate::leanh::lean_inc(v_fst_7237_);
                    crate::leanh::lean_dec(v_snd_7228_);
                    v___x_7240_ = crate::leanh::lean_box(0);
                    v_isShared_7241_ = v_isSharedCheck_7315_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if crate::leanh::lean_obj_tag(v_val_7229_) == 0 {
                    v_fvarId_7258_ = crate::leanh::lean_ctor_get(v_val_7229_, 1);
                    v_userName_7259_ = crate::leanh::lean_ctor_get(v_val_7229_, 2);
                    v_type_7260_ = crate::leanh::lean_ctor_get(v_val_7229_, 3);
                    v_bi_7261_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_7229_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    v_kind_7262_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_7229_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                    );
                    v_isSharedCheck_7279_ = (!crate::leanh::lean_is_exclusive(v_val_7229_)) as u8;
                    if v_isSharedCheck_7279_ == 0 {
                        v_unused_7280_ = crate::leanh::lean_ctor_get(v_val_7229_, 0);
                        crate::leanh::lean_dec(v_unused_7280_);
                        v___x_7264_ = v_val_7229_;
                        v_isShared_7265_ = v_isSharedCheck_7279_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_type_7260_);
                        crate::leanh::lean_inc(v_userName_7259_);
                        crate::leanh::lean_inc(v_fvarId_7258_);
                        crate::leanh::lean_dec(v_val_7229_);
                        v___x_7264_ = crate::leanh::lean_box(0);
                        v_isShared_7265_ = v_isSharedCheck_7279_;
                        state = 11;
                        continue;
                    }
                } else {
                    v_fvarId_7281_ = crate::leanh::lean_ctor_get(v_val_7229_, 1);
                    v_userName_7282_ = crate::leanh::lean_ctor_get(v_val_7229_, 2);
                    v_type_7283_ = crate::leanh::lean_ctor_get(v_val_7229_, 3);
                    v_value_7284_ = crate::leanh::lean_ctor_get(v_val_7229_, 4);
                    v_nondep_7285_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_7229_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    );
                    v_kind_7286_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_7229_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    );
                    v_isSharedCheck_7313_ = (!crate::leanh::lean_is_exclusive(v_val_7229_)) as u8;
                    if v_isSharedCheck_7313_ == 0 {
                        v_unused_7314_ = crate::leanh::lean_ctor_get(v_val_7229_, 0);
                        crate::leanh::lean_dec(v_unused_7314_);
                        v___x_7288_ = v_val_7229_;
                        v_isShared_7289_ = v_isSharedCheck_7313_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_7284_);
                        crate::leanh::lean_inc(v_type_7283_);
                        crate::leanh::lean_inc(v_userName_7282_);
                        crate::leanh::lean_inc(v_fvarId_7281_);
                        crate::leanh::lean_dec(v_val_7229_);
                        v___x_7288_ = crate::leanh::lean_box(0);
                        v_isShared_7289_ = v_isSharedCheck_7313_;
                        state = 15;
                        continue;
                    }
                }
            }
            7 => {
                v___x_7244_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_7245_ = lean_nat_add(v_snd_7238_, v___x_7244_);
                crate::leanh::lean_dec(v_snd_7238_);
                crate::leanh::lean_inc_ref(v_decl_7243_);
                if v_isShared_7232_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7231_, 0, v_decl_7243_);
                    v___x_7247_ = v___x_7231_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7257_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7257_, 0, v_decl_7243_);
                    v___x_7247_ = v_reuseFailAlloc_7257_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_7248_ = l_Lean_PersistentArray_push___redArg(v_fst_7237_, v___x_7247_);
                v___x_7249_ = l_Lean_LocalDecl_fvarId(v_decl_7243_);
                v___x_7250_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_7233_, v___x_7249_, v_decl_7243_);
                if v_isShared_7241_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7240_, 1, v___x_7245_);
                    crate::leanh::lean_ctor_set(v___x_7240_, 0, v___x_7248_);
                    v___x_7252_ = v___x_7240_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7256_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7256_, 0, v___x_7248_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7256_, 1, v___x_7245_);
                    v___x_7252_ = v_reuseFailAlloc_7256_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_7236_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7235_, 1, v___x_7252_);
                    crate::leanh::lean_ctor_set(v___x_7235_, 0, v___x_7250_);
                    v___x_7254_ = v___x_7235_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7255_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7255_, 0, v___x_7250_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7255_, 1, v___x_7252_);
                    v___x_7254_ = v_reuseFailAlloc_7255_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_a_7220_ = v___x_7254_;
                state = 2;
                continue;
            }
            11 => {
                v___x_7266_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(
                    v_type_7260_,
                    v___y_7205_,
                    v___y_7206_,
                    v___y_7207_,
                    v___y_7208_,
                    v___y_7209_,
                    v___y_7210_,
                );
                if crate::leanh::lean_obj_tag(v___x_7266_) == 0 {
                    v_a_7267_ = crate::leanh::lean_ctor_get(v___x_7266_, 0);
                    crate::leanh::lean_inc(v_a_7267_);
                    crate::leanh::lean_dec_ref_known(v___x_7266_, 1);
                    crate::leanh::lean_inc(v_snd_7238_);
                    if v_isShared_7265_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7264_, 3, v_a_7267_);
                        crate::leanh::lean_ctor_set(v___x_7264_, 0, v_snd_7238_);
                        v___x_7269_ = v___x_7264_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_7270_ = crate::leanh::lean_alloc_ctor(0, 4, (2) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7270_, 0, v_snd_7238_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7270_, 1, v_fvarId_7258_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7270_, 2, v_userName_7259_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7270_, 3, v_a_7267_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_7270_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            v_bi_7261_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_7270_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                            v_kind_7262_,
                        );
                        v___x_7269_ = v_reuseFailAlloc_7270_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7264_);
                    crate::leanh::lean_dec(v_userName_7259_);
                    crate::leanh::lean_dec(v_fvarId_7258_);
                    crate::leanh::lean_del_object(v___x_7240_);
                    crate::leanh::lean_dec(v_snd_7238_);
                    crate::leanh::lean_dec(v_fst_7237_);
                    crate::leanh::lean_del_object(v___x_7235_);
                    crate::leanh::lean_dec(v_fst_7233_);
                    crate::leanh::lean_del_object(v___x_7231_);
                    crate::leanh::lean_del_object(v___x_7216_);
                    v_a_7271_ = crate::leanh::lean_ctor_get(v___x_7266_, 0);
                    v_isSharedCheck_7278_ = (!crate::leanh::lean_is_exclusive(v___x_7266_)) as u8;
                    if v_isSharedCheck_7278_ == 0 {
                        v___x_7273_ = v___x_7266_;
                        v_isShared_7274_ = v_isSharedCheck_7278_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7271_);
                        crate::leanh::lean_dec(v___x_7266_);
                        v___x_7273_ = crate::leanh::lean_box(0);
                        v_isShared_7274_ = v_isSharedCheck_7278_;
                        state = 13;
                        continue;
                    }
                }
            }
            12 => {
                v_decl_7243_ = v___x_7269_;
                state = 7;
                continue;
            }
            13 => {
                if v_isShared_7274_ == 0 {
                    v___x_7276_ = v___x_7273_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_7277_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7277_, 0, v_a_7271_);
                    v___x_7276_ = v_reuseFailAlloc_7277_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_7276_;
            }
            15 => {
                v___x_7290_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(
                    v_type_7283_,
                    v___y_7205_,
                    v___y_7206_,
                    v___y_7207_,
                    v___y_7208_,
                    v___y_7209_,
                    v___y_7210_,
                );
                if crate::leanh::lean_obj_tag(v___x_7290_) == 0 {
                    v_a_7291_ = crate::leanh::lean_ctor_get(v___x_7290_, 0);
                    crate::leanh::lean_inc(v_a_7291_);
                    crate::leanh::lean_dec_ref_known(v___x_7290_, 1);
                    v___x_7292_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(
                        v_value_7284_,
                        v___y_7205_,
                        v___y_7206_,
                        v___y_7207_,
                        v___y_7208_,
                        v___y_7209_,
                        v___y_7210_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7292_) == 0 {
                        v_a_7293_ = crate::leanh::lean_ctor_get(v___x_7292_, 0);
                        crate::leanh::lean_inc(v_a_7293_);
                        crate::leanh::lean_dec_ref_known(v___x_7292_, 1);
                        crate::leanh::lean_inc(v_snd_7238_);
                        if v_isShared_7289_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_7288_, 4, v_a_7293_);
                            crate::leanh::lean_ctor_set(v___x_7288_, 3, v_a_7291_);
                            crate::leanh::lean_ctor_set(v___x_7288_, 0, v_snd_7238_);
                            v___x_7295_ = v___x_7288_;
                            state = 16;
                            continue;
                        } else {
                            v_reuseFailAlloc_7296_ =
                                crate::leanh::lean_alloc_ctor(1, 5, (2) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7296_, 0, v_snd_7238_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7296_, 1, v_fvarId_7281_);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_7296_,
                                2,
                                v_userName_7282_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7296_, 3, v_a_7291_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7296_, 4, v_a_7293_);
                            crate::leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_7296_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                                v_nondep_7285_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_7296_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1)
                                    as u32,
                                v_kind_7286_,
                            );
                            v___x_7295_ = v_reuseFailAlloc_7296_;
                            state = 16;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_7291_);
                        crate::leanh::lean_del_object(v___x_7288_);
                        crate::leanh::lean_dec(v_userName_7282_);
                        crate::leanh::lean_dec(v_fvarId_7281_);
                        crate::leanh::lean_del_object(v___x_7240_);
                        crate::leanh::lean_dec(v_snd_7238_);
                        crate::leanh::lean_dec(v_fst_7237_);
                        crate::leanh::lean_del_object(v___x_7235_);
                        crate::leanh::lean_dec(v_fst_7233_);
                        crate::leanh::lean_del_object(v___x_7231_);
                        crate::leanh::lean_del_object(v___x_7216_);
                        v_a_7297_ = crate::leanh::lean_ctor_get(v___x_7292_, 0);
                        v_isSharedCheck_7304_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7292_)) as u8;
                        if v_isSharedCheck_7304_ == 0 {
                            v___x_7299_ = v___x_7292_;
                            v_isShared_7300_ = v_isSharedCheck_7304_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7297_);
                            crate::leanh::lean_dec(v___x_7292_);
                            v___x_7299_ = crate::leanh::lean_box(0);
                            v_isShared_7300_ = v_isSharedCheck_7304_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7288_);
                    crate::leanh::lean_dec_ref(v_value_7284_);
                    crate::leanh::lean_dec(v_userName_7282_);
                    crate::leanh::lean_dec(v_fvarId_7281_);
                    crate::leanh::lean_del_object(v___x_7240_);
                    crate::leanh::lean_dec(v_snd_7238_);
                    crate::leanh::lean_dec(v_fst_7237_);
                    crate::leanh::lean_del_object(v___x_7235_);
                    crate::leanh::lean_dec(v_fst_7233_);
                    crate::leanh::lean_del_object(v___x_7231_);
                    crate::leanh::lean_del_object(v___x_7216_);
                    v_a_7305_ = crate::leanh::lean_ctor_get(v___x_7290_, 0);
                    v_isSharedCheck_7312_ = (!crate::leanh::lean_is_exclusive(v___x_7290_)) as u8;
                    if v_isSharedCheck_7312_ == 0 {
                        v___x_7307_ = v___x_7290_;
                        v_isShared_7308_ = v_isSharedCheck_7312_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7305_);
                        crate::leanh::lean_dec(v___x_7290_);
                        v___x_7307_ = crate::leanh::lean_box(0);
                        v_isShared_7308_ = v_isSharedCheck_7312_;
                        state = 19;
                        continue;
                    }
                }
            }
            16 => {
                v_decl_7243_ = v___x_7295_;
                state = 7;
                continue;
            }
            17 => {
                if v_isShared_7300_ == 0 {
                    v___x_7302_ = v___x_7299_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_7303_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7303_, 0, v_a_7297_);
                    v___x_7302_ = v_reuseFailAlloc_7303_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_7302_;
            }
            19 => {
                if v_isShared_7308_ == 0 {
                    v___x_7310_ = v___x_7307_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_7311_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7311_, 0, v_a_7305_);
                    v___x_7310_ = v_reuseFailAlloc_7311_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_7310_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3___boxed(
    mut v_as_7321_: *mut crate::leanh::LeanObject,
    mut v_sz_7322_: *mut crate::leanh::LeanObject,
    mut v_i_7323_: *mut crate::leanh::LeanObject,
    mut v_b_7324_: *mut crate::leanh::LeanObject,
    mut v___y_7325_: *mut crate::leanh::LeanObject,
    mut v___y_7326_: *mut crate::leanh::LeanObject,
    mut v___y_7327_: *mut crate::leanh::LeanObject,
    mut v___y_7328_: *mut crate::leanh::LeanObject,
    mut v___y_7329_: *mut crate::leanh::LeanObject,
    mut v___y_7330_: *mut crate::leanh::LeanObject,
    mut v___y_7331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_7332_: usize = 0;
    let mut v_i_boxed_7333_: usize = 0;
    let mut v_res_7334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7332_ = crate::leanh::lean_unbox_usize(v_sz_7322_);
    crate::leanh::lean_dec(v_sz_7322_);
    v_i_boxed_7333_ = crate::leanh::lean_unbox_usize(v_i_7323_);
    crate::leanh::lean_dec(v_i_7323_);
    v_res_7334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(v_as_7321_, v_sz_boxed_7332_, v_i_boxed_7333_, v_b_7324_, v___y_7325_, v___y_7326_, v___y_7327_, v___y_7328_, v___y_7329_, v___y_7330_);
    crate::leanh::lean_dec(v___y_7330_);
    crate::leanh::lean_dec_ref(v___y_7329_);
    crate::leanh::lean_dec(v___y_7328_);
    crate::leanh::lean_dec_ref(v___y_7327_);
    crate::leanh::lean_dec(v___y_7326_);
    crate::leanh::lean_dec_ref(v___y_7325_);
    crate::leanh::lean_dec_ref(v_as_7321_);
    return v_res_7334_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(
    mut v_t_7335_: *mut crate::leanh::LeanObject,
    mut v_init_7336_: *mut crate::leanh::LeanObject,
    mut v___y_7337_: *mut crate::leanh::LeanObject,
    mut v___y_7338_: *mut crate::leanh::LeanObject,
    mut v___y_7339_: *mut crate::leanh::LeanObject,
    mut v___y_7340_: *mut crate::leanh::LeanObject,
    mut v___y_7341_: *mut crate::leanh::LeanObject,
    mut v___y_7342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_7344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7350_: u8 = 0;
    let mut v_a_7351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7358_: usize = 0;
    let mut v___x_7359_: usize = 0;
    let mut v___x_7360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7364_: u8 = 0;
    let mut v_fst_7365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7374_: u8 = 0;
    let mut v_a_7375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7378_: u8 = 0;
    let mut v___x_7380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7382_: u8 = 0;
    let mut v_isSharedCheck_7383_: u8 = 0;
    let mut v_a_7384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7387_: u8 = 0;
    let mut v___x_7389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7391_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_7344_ = crate::leanh::lean_ctor_get(v_t_7335_, 0);
                v_tail_7345_ = crate::leanh::lean_ctor_get(v_t_7335_, 1);
                crate::leanh::lean_inc_ref(v_init_7336_);
                v___x_7346_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_init_7336_, v_root_7344_, v_init_7336_, v___y_7337_, v___y_7338_, v___y_7339_, v___y_7340_, v___y_7341_, v___y_7342_);
                crate::leanh::lean_dec_ref(v_init_7336_);
                if crate::leanh::lean_obj_tag(v___x_7346_) == 0 {
                    v_a_7347_ = crate::leanh::lean_ctor_get(v___x_7346_, 0);
                    v_isSharedCheck_7383_ = (!crate::leanh::lean_is_exclusive(v___x_7346_)) as u8;
                    if v_isSharedCheck_7383_ == 0 {
                        v___x_7349_ = v___x_7346_;
                        v_isShared_7350_ = v_isSharedCheck_7383_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7347_);
                        crate::leanh::lean_dec(v___x_7346_);
                        v___x_7349_ = crate::leanh::lean_box(0);
                        v_isShared_7350_ = v_isSharedCheck_7383_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7384_ = crate::leanh::lean_ctor_get(v___x_7346_, 0);
                    v_isSharedCheck_7391_ = (!crate::leanh::lean_is_exclusive(v___x_7346_)) as u8;
                    if v_isSharedCheck_7391_ == 0 {
                        v___x_7386_ = v___x_7346_;
                        v_isShared_7387_ = v_isSharedCheck_7391_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7384_);
                        crate::leanh::lean_dec(v___x_7346_);
                        v___x_7386_ = crate::leanh::lean_box(0);
                        v_isShared_7387_ = v_isSharedCheck_7391_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_7347_) == 0 {
                    v_a_7351_ = crate::leanh::lean_ctor_get(v_a_7347_, 0);
                    crate::leanh::lean_inc(v_a_7351_);
                    crate::leanh::lean_dec_ref_known(v_a_7347_, 1);
                    if v_isShared_7350_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7349_, 0, v_a_7351_);
                        v___x_7353_ = v___x_7349_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7354_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7354_, 0, v_a_7351_);
                        v___x_7353_ = v_reuseFailAlloc_7354_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7349_);
                    v_a_7355_ = crate::leanh::lean_ctor_get(v_a_7347_, 0);
                    crate::leanh::lean_inc(v_a_7355_);
                    crate::leanh::lean_dec_ref_known(v_a_7347_, 1);
                    v___x_7356_ = crate::leanh::lean_box(0);
                    v___x_7357_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7357_, 0, v___x_7356_);
                    crate::leanh::lean_ctor_set(v___x_7357_, 1, v_a_7355_);
                    v_sz_7358_ = lean_array_size(v_tail_7345_);
                    v___x_7359_ = 0usize;
                    v___x_7360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(v_tail_7345_, v_sz_7358_, v___x_7359_, v___x_7357_, v___y_7337_, v___y_7338_, v___y_7339_, v___y_7340_, v___y_7341_, v___y_7342_);
                    if crate::leanh::lean_obj_tag(v___x_7360_) == 0 {
                        v_a_7361_ = crate::leanh::lean_ctor_get(v___x_7360_, 0);
                        v_isSharedCheck_7374_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7360_)) as u8;
                        if v_isSharedCheck_7374_ == 0 {
                            v___x_7363_ = v___x_7360_;
                            v_isShared_7364_ = v_isSharedCheck_7374_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7361_);
                            crate::leanh::lean_dec(v___x_7360_);
                            v___x_7363_ = crate::leanh::lean_box(0);
                            v_isShared_7364_ = v_isSharedCheck_7374_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_7375_ = crate::leanh::lean_ctor_get(v___x_7360_, 0);
                        v_isSharedCheck_7382_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7360_)) as u8;
                        if v_isSharedCheck_7382_ == 0 {
                            v___x_7377_ = v___x_7360_;
                            v_isShared_7378_ = v_isSharedCheck_7382_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7375_);
                            crate::leanh::lean_dec(v___x_7360_);
                            v___x_7377_ = crate::leanh::lean_box(0);
                            v_isShared_7378_ = v_isSharedCheck_7382_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_7353_;
            }
            3 => {
                v_fst_7365_ = crate::leanh::lean_ctor_get(v_a_7361_, 0);
                if crate::leanh::lean_obj_tag(v_fst_7365_) == 0 {
                    v_snd_7366_ = crate::leanh::lean_ctor_get(v_a_7361_, 1);
                    crate::leanh::lean_inc(v_snd_7366_);
                    crate::leanh::lean_dec(v_a_7361_);
                    if v_isShared_7364_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7363_, 0, v_snd_7366_);
                        v___x_7368_ = v___x_7363_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_7369_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7369_, 0, v_snd_7366_);
                        v___x_7368_ = v_reuseFailAlloc_7369_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_7365_);
                    crate::leanh::lean_dec(v_a_7361_);
                    v_val_7370_ = crate::leanh::lean_ctor_get(v_fst_7365_, 0);
                    crate::leanh::lean_inc(v_val_7370_);
                    crate::leanh::lean_dec_ref_known(v_fst_7365_, 1);
                    if v_isShared_7364_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7363_, 0, v_val_7370_);
                        v___x_7372_ = v___x_7363_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_7373_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7373_, 0, v_val_7370_);
                        v___x_7372_ = v_reuseFailAlloc_7373_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_7368_;
            }
            5 => {
                return v___x_7372_;
            }
            6 => {
                if v_isShared_7378_ == 0 {
                    v___x_7380_ = v___x_7377_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7381_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7381_, 0, v_a_7375_);
                    v___x_7380_ = v_reuseFailAlloc_7381_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7380_;
            }
            8 => {
                if v_isShared_7387_ == 0 {
                    v___x_7389_ = v___x_7386_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7390_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7390_, 0, v_a_7384_);
                    v___x_7389_ = v_reuseFailAlloc_7390_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7389_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1___boxed(
    mut v_t_7392_: *mut crate::leanh::LeanObject,
    mut v_init_7393_: *mut crate::leanh::LeanObject,
    mut v___y_7394_: *mut crate::leanh::LeanObject,
    mut v___y_7395_: *mut crate::leanh::LeanObject,
    mut v___y_7396_: *mut crate::leanh::LeanObject,
    mut v___y_7397_: *mut crate::leanh::LeanObject,
    mut v___y_7398_: *mut crate::leanh::LeanObject,
    mut v___y_7399_: *mut crate::leanh::LeanObject,
    mut v___y_7400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7401_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(v_t_7392_, v_init_7393_, v___y_7394_, v___y_7395_, v___y_7396_, v___y_7397_, v___y_7398_, v___y_7399_);
    crate::leanh::lean_dec(v___y_7399_);
    crate::leanh::lean_dec_ref(v___y_7398_);
    crate::leanh::lean_dec(v___y_7397_);
    crate::leanh::lean_dec_ref(v___y_7396_);
    crate::leanh::lean_dec(v___y_7395_);
    crate::leanh::lean_dec_ref(v___y_7394_);
    crate::leanh::lean_dec_ref(v_t_7392_);
    return v_res_7401_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7402_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_7403_ = lean_mk_empty_array_with_capacity(v___x_7402_);
    v___x_7404_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7404_, 0, v___x_7403_);
    return v___x_7404_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7405_: usize = 0;
    let mut v_index_7406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_7410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7405_ = 5usize;
    v_index_7406_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_7407_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_7408_ = lean_mk_empty_array_with_capacity(v___x_7407_);
    v___x_7409_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0_once
        ),
        _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0,
    );
    v_decls_7410_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v_decls_7410_, 0, v___x_7409_);
    crate::leanh::lean_ctor_set(v_decls_7410_, 1, v___x_7408_);
    crate::leanh::lean_ctor_set(v_decls_7410_, 2, v_index_7406_);
    crate::leanh::lean_ctor_set(v_decls_7410_, 3, v_index_7406_);
    crate::leanh::lean_ctor_set_usize(v_decls_7410_, 4, v___x_7405_);
    return v_decls_7410_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7411_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_7411_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarIdToDecl_7413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7412_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2_once
        ),
        _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2,
    );
    v_fvarIdToDecl_7413_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v_fvarIdToDecl_7413_, 0, v___x_7412_);
    return v_fvarIdToDecl_7413_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v_index_7414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_7415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_index_7414_ = crate::leanh::lean_unsigned_to_nat(0);
    v_decls_7415_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1_once
        ),
        _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1,
    );
    v___x_7416_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7416_, 0, v_decls_7415_);
    crate::leanh::lean_ctor_set(v___x_7416_, 1, v_index_7414_);
    return v___x_7416_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarIdToDecl_7418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7417_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4_once
        ),
        _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4,
    );
    v_fvarIdToDecl_7418_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3_once
        ),
        _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3,
    );
    v___x_7419_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7419_, 0, v_fvarIdToDecl_7418_);
    crate::leanh::lean_ctor_set(v___x_7419_, 1, v___x_7417_);
    return v___x_7419_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(
    mut v_lctx_7420_: *mut crate::leanh::LeanObject,
    mut v_a_7421_: *mut crate::leanh::LeanObject,
    mut v_a_7422_: *mut crate::leanh::LeanObject,
    mut v_a_7423_: *mut crate::leanh::LeanObject,
    mut v_a_7424_: *mut crate::leanh::LeanObject,
    mut v_a_7425_: *mut crate::leanh::LeanObject,
    mut v_a_7426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decls_7428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclToFullName_7429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7432_: u8 = 0;
    let mut v___x_7433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7438_: u8 = 0;
    let mut v_snd_7439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7448_: u8 = 0;
    let mut v_a_7449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7452_: u8 = 0;
    let mut v___x_7454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7456_: u8 = 0;
    let mut v_isSharedCheck_7457_: u8 = 0;
    let mut v_unused_7458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_decls_7428_ = crate::leanh::lean_ctor_get(v_lctx_7420_, 1);
                v_auxDeclToFullName_7429_ = crate::leanh::lean_ctor_get(v_lctx_7420_, 2);
                v_isSharedCheck_7457_ = (!crate::leanh::lean_is_exclusive(v_lctx_7420_)) as u8;
                if v_isSharedCheck_7457_ == 0 {
                    v_unused_7458_ = crate::leanh::lean_ctor_get(v_lctx_7420_, 0);
                    crate::leanh::lean_dec(v_unused_7458_);
                    v___x_7431_ = v_lctx_7420_;
                    v_isShared_7432_ = v_isSharedCheck_7457_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_auxDeclToFullName_7429_);
                    crate::leanh::lean_inc(v_decls_7428_);
                    crate::leanh::lean_dec(v_lctx_7420_);
                    v___x_7431_ = crate::leanh::lean_box(0);
                    v_isShared_7432_ = v_isSharedCheck_7457_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7433_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5_once), _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5);
                v___x_7434_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(v_decls_7428_, v___x_7433_, v_a_7421_, v_a_7422_, v_a_7423_, v_a_7424_, v_a_7425_, v_a_7426_);
                crate::leanh::lean_dec_ref(v_decls_7428_);
                if crate::leanh::lean_obj_tag(v___x_7434_) == 0 {
                    v_a_7435_ = crate::leanh::lean_ctor_get(v___x_7434_, 0);
                    v_isSharedCheck_7448_ = (!crate::leanh::lean_is_exclusive(v___x_7434_)) as u8;
                    if v_isSharedCheck_7448_ == 0 {
                        v___x_7437_ = v___x_7434_;
                        v_isShared_7438_ = v_isSharedCheck_7448_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7435_);
                        crate::leanh::lean_dec(v___x_7434_);
                        v___x_7437_ = crate::leanh::lean_box(0);
                        v_isShared_7438_ = v_isSharedCheck_7448_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7431_);
                    crate::leanh::lean_dec(v_auxDeclToFullName_7429_);
                    v_a_7449_ = crate::leanh::lean_ctor_get(v___x_7434_, 0);
                    v_isSharedCheck_7456_ = (!crate::leanh::lean_is_exclusive(v___x_7434_)) as u8;
                    if v_isSharedCheck_7456_ == 0 {
                        v___x_7451_ = v___x_7434_;
                        v_isShared_7452_ = v_isSharedCheck_7456_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7449_);
                        crate::leanh::lean_dec(v___x_7434_);
                        v___x_7451_ = crate::leanh::lean_box(0);
                        v_isShared_7452_ = v_isSharedCheck_7456_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_7439_ = crate::leanh::lean_ctor_get(v_a_7435_, 1);
                crate::leanh::lean_inc(v_snd_7439_);
                v_fst_7440_ = crate::leanh::lean_ctor_get(v_a_7435_, 0);
                crate::leanh::lean_inc(v_fst_7440_);
                crate::leanh::lean_dec(v_a_7435_);
                v_fst_7441_ = crate::leanh::lean_ctor_get(v_snd_7439_, 0);
                crate::leanh::lean_inc(v_fst_7441_);
                crate::leanh::lean_dec(v_snd_7439_);
                if v_isShared_7432_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7431_, 1, v_fst_7441_);
                    crate::leanh::lean_ctor_set(v___x_7431_, 0, v_fst_7440_);
                    v___x_7443_ = v___x_7431_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7447_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7447_, 0, v_fst_7440_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7447_, 1, v_fst_7441_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_7447_,
                        2,
                        v_auxDeclToFullName_7429_,
                    );
                    v___x_7443_ = v_reuseFailAlloc_7447_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_7438_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7437_, 0, v___x_7443_);
                    v___x_7445_ = v___x_7437_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7446_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7446_, 0, v___x_7443_);
                    v___x_7445_ = v_reuseFailAlloc_7446_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7445_;
            }
            5 => {
                if v_isShared_7452_ == 0 {
                    v___x_7454_ = v___x_7451_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7455_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7455_, 0, v_a_7449_);
                    v___x_7454_ = v_reuseFailAlloc_7455_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7454_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___boxed(
    mut v_lctx_7459_: *mut crate::leanh::LeanObject,
    mut v_a_7460_: *mut crate::leanh::LeanObject,
    mut v_a_7461_: *mut crate::leanh::LeanObject,
    mut v_a_7462_: *mut crate::leanh::LeanObject,
    mut v_a_7463_: *mut crate::leanh::LeanObject,
    mut v_a_7464_: *mut crate::leanh::LeanObject,
    mut v_a_7465_: *mut crate::leanh::LeanObject,
    mut v_a_7466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7467_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(
        v_lctx_7459_,
        v_a_7460_,
        v_a_7461_,
        v_a_7462_,
        v_a_7463_,
        v_a_7464_,
        v_a_7465_,
    );
    crate::leanh::lean_dec(v_a_7465_);
    crate::leanh::lean_dec_ref(v_a_7464_);
    crate::leanh::lean_dec(v_a_7463_);
    crate::leanh::lean_dec_ref(v_a_7462_);
    crate::leanh::lean_dec(v_a_7461_);
    crate::leanh::lean_dec_ref(v_a_7460_);
    return v_res_7467_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0(
    mut v_00_u03b2_7468_: *mut crate::leanh::LeanObject,
    mut v_x_7469_: *mut crate::leanh::LeanObject,
    mut v_x_7470_: *mut crate::leanh::LeanObject,
    mut v_x_7471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7472_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_x_7469_, v_x_7470_, v_x_7471_);
    return v___x_7472_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0(
    mut v_00_u03b2_7473_: *mut crate::leanh::LeanObject,
    mut v_x_7474_: *mut crate::leanh::LeanObject,
    mut v_x_7475_: usize,
    mut v_x_7476_: usize,
    mut v_x_7477_: *mut crate::leanh::LeanObject,
    mut v_x_7478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7479_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_x_7474_, v_x_7475_, v_x_7476_, v_x_7477_, v_x_7478_);
    return v___x_7479_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___boxed(
    mut v_00_u03b2_7480_: *mut crate::leanh::LeanObject,
    mut v_x_7481_: *mut crate::leanh::LeanObject,
    mut v_x_7482_: *mut crate::leanh::LeanObject,
    mut v_x_7483_: *mut crate::leanh::LeanObject,
    mut v_x_7484_: *mut crate::leanh::LeanObject,
    mut v_x_7485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_10744__boxed_7486_: usize = 0;
    let mut v_x_10745__boxed_7487_: usize = 0;
    let mut v_res_7488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_10744__boxed_7486_ = crate::leanh::lean_unbox_usize(v_x_7482_);
    crate::leanh::lean_dec(v_x_7482_);
    v_x_10745__boxed_7487_ = crate::leanh::lean_unbox_usize(v_x_7483_);
    crate::leanh::lean_dec(v_x_7483_);
    v_res_7488_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0(v_00_u03b2_7480_, v_x_7481_, v_x_10744__boxed_7486_, v_x_10745__boxed_7487_, v_x_7484_, v_x_7485_);
    return v_res_7488_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1(
    mut v_00_u03b2_7489_: *mut crate::leanh::LeanObject,
    mut v_n_7490_: *mut crate::leanh::LeanObject,
    mut v_k_7491_: *mut crate::leanh::LeanObject,
    mut v_v_7492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7493_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1___redArg(v_n_7490_, v_k_7491_, v_v_7492_);
    return v___x_7493_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2(
    mut v_00_u03b2_7494_: *mut crate::leanh::LeanObject,
    mut v_depth_7495_: usize,
    mut v_keys_7496_: *mut crate::leanh::LeanObject,
    mut v_vals_7497_: *mut crate::leanh::LeanObject,
    mut v_heq_7498_: *mut crate::leanh::LeanObject,
    mut v_i_7499_: *mut crate::leanh::LeanObject,
    mut v_entries_7500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7501_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(v_depth_7495_, v_keys_7496_, v_vals_7497_, v_i_7499_, v_entries_7500_);
    return v___x_7501_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_7502_: *mut crate::leanh::LeanObject,
    mut v_depth_7503_: *mut crate::leanh::LeanObject,
    mut v_keys_7504_: *mut crate::leanh::LeanObject,
    mut v_vals_7505_: *mut crate::leanh::LeanObject,
    mut v_heq_7506_: *mut crate::leanh::LeanObject,
    mut v_i_7507_: *mut crate::leanh::LeanObject,
    mut v_entries_7508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_7509_: usize = 0;
    let mut v_res_7510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_7509_ = crate::leanh::lean_unbox_usize(v_depth_7503_);
    crate::leanh::lean_dec(v_depth_7503_);
    v_res_7510_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2(v_00_u03b2_7502_, v_depth_boxed_7509_, v_keys_7504_, v_vals_7505_, v_heq_7506_, v_i_7507_, v_entries_7508_);
    crate::leanh::lean_dec_ref(v_vals_7505_);
    crate::leanh::lean_dec_ref(v_keys_7504_);
    return v_res_7510_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_7511_: *mut crate::leanh::LeanObject,
    mut v_x_7512_: *mut crate::leanh::LeanObject,
    mut v_x_7513_: *mut crate::leanh::LeanObject,
    mut v_x_7514_: *mut crate::leanh::LeanObject,
    mut v_x_7515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7516_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3___redArg(v_x_7512_, v_x_7513_, v_x_7514_, v_x_7515_);
    return v___x_7516_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_7517_: *mut crate::leanh::LeanObject,
    mut v_x_7518_: *mut crate::leanh::LeanObject,
    mut v_x_7519_: *mut crate::leanh::LeanObject,
    mut v_x_7520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_7521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_7522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7525_: u8 = 0;
    let mut v___x_7526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7527_: u8 = 0;
    let mut v___x_7528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_7533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7534_: u8 = 0;
    let mut v___x_7536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7546_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_7521_ = crate::leanh::lean_ctor_get(v_x_7517_, 0);
                v_vs_7522_ = crate::leanh::lean_ctor_get(v_x_7517_, 1);
                v_isSharedCheck_7546_ = (!crate::leanh::lean_is_exclusive(v_x_7517_)) as u8;
                if v_isSharedCheck_7546_ == 0 {
                    v___x_7524_ = v_x_7517_;
                    v_isShared_7525_ = v_isSharedCheck_7546_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_7522_);
                    crate::leanh::lean_inc(v_ks_7521_);
                    crate::leanh::lean_dec(v_x_7517_);
                    v___x_7524_ = crate::leanh::lean_box(0);
                    v_isShared_7525_ = v_isSharedCheck_7546_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7526_ = lean_array_get_size(v_ks_7521_);
                v___x_7527_ = lean_nat_dec_lt(v_x_7518_, v___x_7526_);
                if v___x_7527_ == 0 {
                    crate::leanh::lean_dec(v_x_7518_);
                    v___x_7528_ = lean_array_push(v_ks_7521_, v_x_7519_);
                    v___x_7529_ = lean_array_push(v_vs_7522_, v_x_7520_);
                    if v_isShared_7525_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7524_, 1, v___x_7529_);
                        crate::leanh::lean_ctor_set(v___x_7524_, 0, v___x_7528_);
                        v___x_7531_ = v___x_7524_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7532_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7532_, 0, v___x_7528_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7532_, 1, v___x_7529_);
                        v___x_7531_ = v_reuseFailAlloc_7532_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_7533_ = lean_array_fget_borrowed(v_ks_7521_, v_x_7518_);
                    v___x_7534_ = l_Lean_instBEqMVarId_beq(v_x_7519_, v_k_x27_7533_);
                    if v___x_7534_ == 0 {
                        if v_isShared_7525_ == 0 {
                            v___x_7536_ = v___x_7524_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_7540_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7540_, 0, v_ks_7521_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7540_, 1, v_vs_7522_);
                            v___x_7536_ = v_reuseFailAlloc_7540_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_7541_ = lean_array_fset(v_ks_7521_, v_x_7518_, v_x_7519_);
                        v___x_7542_ = lean_array_fset(v_vs_7522_, v_x_7518_, v_x_7520_);
                        crate::leanh::lean_dec(v_x_7518_);
                        if v_isShared_7525_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_7524_, 1, v___x_7542_);
                            crate::leanh::lean_ctor_set(v___x_7524_, 0, v___x_7541_);
                            v___x_7544_ = v___x_7524_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_7545_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7545_, 0, v___x_7541_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7545_, 1, v___x_7542_);
                            v___x_7544_ = v_reuseFailAlloc_7545_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_7531_;
            }
            3 => {
                v___x_7537_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_7538_ = lean_nat_add(v_x_7518_, v___x_7537_);
                crate::leanh::lean_dec(v_x_7518_);
                v_x_7517_ = v___x_7536_;
                v_x_7518_ = v___x_7538_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_7544_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_n_7547_: *mut crate::leanh::LeanObject,
    mut v_k_7548_: *mut crate::leanh::LeanObject,
    mut v_v_7549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7550_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_7551_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_7547_, v___x_7550_, v_k_7548_, v_v_7549_);
    return v___x_7551_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(
    mut v_x_7552_: *mut crate::leanh::LeanObject,
    mut v_x_7553_: usize,
    mut v_x_7554_: usize,
    mut v_x_7555_: *mut crate::leanh::LeanObject,
    mut v_x_7556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_7557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7558_: usize = 0;
    let mut v___x_7559_: usize = 0;
    let mut v___x_7560_: usize = 0;
    let mut v___x_7561_: usize = 0;
    let mut v_j_7562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7564_: u8 = 0;
    let mut v___x_7566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7567_: u8 = 0;
    let mut v_v_7568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_7570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_7577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7581_: u8 = 0;
    let mut v___x_7582_: u8 = 0;
    let mut v___x_7583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7588_: u8 = 0;
    let mut v_node_7589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7592_: u8 = 0;
    let mut v___x_7593_: usize = 0;
    let mut v___x_7594_: usize = 0;
    let mut v___x_7595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7599_: u8 = 0;
    let mut v___x_7600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7601_: u8 = 0;
    let mut v_unused_7602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_7603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_7604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7607_: u8 = 0;
    let mut v___x_7609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_7610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7612_: u8 = 0;
    let mut v_ks_7613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_7614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7618_: usize = 0;
    let mut v___x_7619_: u8 = 0;
    let mut v___x_7620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7622_: u8 = 0;
    let mut v_reuseFailAlloc_7623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7624_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_7552_) == 0 {
                    v_es_7557_ = crate::leanh::lean_ctor_get(v_x_7552_, 0);
                    v___x_7558_ = 5usize;
                    v___x_7559_ = 1usize;
                    v___x_7560_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1);
                    v___x_7561_ = lean_usize_land(v_x_7553_, v___x_7560_);
                    v_j_7562_ = lean_usize_to_nat(v___x_7561_);
                    v___x_7563_ = lean_array_get_size(v_es_7557_);
                    v___x_7564_ = lean_nat_dec_lt(v_j_7562_, v___x_7563_);
                    if v___x_7564_ == 0 {
                        crate::leanh::lean_dec(v_j_7562_);
                        crate::leanh::lean_dec(v_x_7556_);
                        crate::leanh::lean_dec(v_x_7555_);
                        return v_x_7552_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_7557_);
                        v_isSharedCheck_7601_ = (!crate::leanh::lean_is_exclusive(v_x_7552_)) as u8;
                        if v_isSharedCheck_7601_ == 0 {
                            v_unused_7602_ = crate::leanh::lean_ctor_get(v_x_7552_, 0);
                            crate::leanh::lean_dec(v_unused_7602_);
                            v___x_7566_ = v_x_7552_;
                            v_isShared_7567_ = v_isSharedCheck_7601_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_7552_);
                            v___x_7566_ = crate::leanh::lean_box(0);
                            v_isShared_7567_ = v_isSharedCheck_7601_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_7603_ = crate::leanh::lean_ctor_get(v_x_7552_, 0);
                    v_vs_7604_ = crate::leanh::lean_ctor_get(v_x_7552_, 1);
                    v_isSharedCheck_7624_ = (!crate::leanh::lean_is_exclusive(v_x_7552_)) as u8;
                    if v_isSharedCheck_7624_ == 0 {
                        v___x_7606_ = v_x_7552_;
                        v_isShared_7607_ = v_isSharedCheck_7624_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_7604_);
                        crate::leanh::lean_inc(v_ks_7603_);
                        crate::leanh::lean_dec(v_x_7552_);
                        v___x_7606_ = crate::leanh::lean_box(0);
                        v_isShared_7607_ = v_isSharedCheck_7624_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_7568_ = lean_array_fget(v_es_7557_, v_j_7562_);
                v___x_7569_ = crate::leanh::lean_box(0);
                v_xs_x27_7570_ = lean_array_fset(v_es_7557_, v_j_7562_, v___x_7569_);
                match crate::leanh::lean_obj_tag(v_v_7568_) {
                    0 => {
                        v_key_7577_ = crate::leanh::lean_ctor_get(v_v_7568_, 0);
                        v_val_7578_ = crate::leanh::lean_ctor_get(v_v_7568_, 1);
                        v_isSharedCheck_7588_ = (!crate::leanh::lean_is_exclusive(v_v_7568_)) as u8;
                        if v_isSharedCheck_7588_ == 0 {
                            v___x_7580_ = v_v_7568_;
                            v_isShared_7581_ = v_isSharedCheck_7588_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_7578_);
                            crate::leanh::lean_inc(v_key_7577_);
                            crate::leanh::lean_dec(v_v_7568_);
                            v___x_7580_ = crate::leanh::lean_box(0);
                            v_isShared_7581_ = v_isSharedCheck_7588_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_7589_ = crate::leanh::lean_ctor_get(v_v_7568_, 0);
                        v_isSharedCheck_7599_ = (!crate::leanh::lean_is_exclusive(v_v_7568_)) as u8;
                        if v_isSharedCheck_7599_ == 0 {
                            v___x_7591_ = v_v_7568_;
                            v_isShared_7592_ = v_isSharedCheck_7599_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_7589_);
                            crate::leanh::lean_dec(v_v_7568_);
                            v___x_7591_ = crate::leanh::lean_box(0);
                            v_isShared_7592_ = v_isSharedCheck_7599_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_7600_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7600_, 0, v_x_7555_);
                        crate::leanh::lean_ctor_set(v___x_7600_, 1, v_x_7556_);
                        v___y_7572_ = v___x_7600_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_7573_ = lean_array_fset(v_xs_x27_7570_, v_j_7562_, v___y_7572_);
                crate::leanh::lean_dec(v_j_7562_);
                if v_isShared_7567_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7566_, 0, v___x_7573_);
                    v___x_7575_ = v___x_7566_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7576_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7576_, 0, v___x_7573_);
                    v___x_7575_ = v_reuseFailAlloc_7576_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7575_;
            }
            4 => {
                v___x_7582_ = l_Lean_instBEqMVarId_beq(v_x_7555_, v_key_7577_);
                if v___x_7582_ == 0 {
                    crate::leanh::lean_del_object(v___x_7580_);
                    v___x_7583_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_7577_,
                        v_val_7578_,
                        v_x_7555_,
                        v_x_7556_,
                    );
                    v___x_7584_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7584_, 0, v___x_7583_);
                    v___y_7572_ = v___x_7584_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_7578_);
                    crate::leanh::lean_dec(v_key_7577_);
                    if v_isShared_7581_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7580_, 1, v_x_7556_);
                        crate::leanh::lean_ctor_set(v___x_7580_, 0, v_x_7555_);
                        v___x_7586_ = v___x_7580_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_7587_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7587_, 0, v_x_7555_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7587_, 1, v_x_7556_);
                        v___x_7586_ = v_reuseFailAlloc_7587_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_7572_ = v___x_7586_;
                state = 2;
                continue;
            }
            6 => {
                v___x_7593_ = lean_usize_shift_right(v_x_7553_, v___x_7558_);
                v___x_7594_ = lean_usize_add(v_x_7554_, v___x_7559_);
                v___x_7595_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_node_7589_, v___x_7593_, v___x_7594_, v_x_7555_, v_x_7556_);
                if v_isShared_7592_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7591_, 0, v___x_7595_);
                    v___x_7597_ = v___x_7591_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7598_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7598_, 0, v___x_7595_);
                    v___x_7597_ = v_reuseFailAlloc_7598_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_7572_ = v___x_7597_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_7607_ == 0 {
                    v___x_7609_ = v___x_7606_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7623_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7623_, 0, v_ks_7603_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7623_, 1, v_vs_7604_);
                    v___x_7609_ = v_reuseFailAlloc_7623_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_7610_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(v___x_7609_, v_x_7555_, v_x_7556_);
                v___x_7618_ = 7usize;
                v___x_7619_ = lean_usize_dec_le(v___x_7618_, v_x_7554_);
                if v___x_7619_ == 0 {
                    v___x_7620_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_7610_);
                    v___x_7621_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_7622_ = lean_nat_dec_lt(v___x_7620_, v___x_7621_);
                    crate::leanh::lean_dec(v___x_7620_);
                    v___y_7612_ = v___x_7622_;
                    state = 10;
                    continue;
                } else {
                    v___y_7612_ = v___x_7619_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_7612_ == 0 {
                    v_ks_7613_ = crate::leanh::lean_ctor_get(v_newNode_7610_, 0);
                    crate::leanh::lean_inc_ref(v_ks_7613_);
                    v_vs_7614_ = crate::leanh::lean_ctor_get(v_newNode_7610_, 1);
                    crate::leanh::lean_inc_ref(v_vs_7614_);
                    crate::leanh::lean_dec_ref(v_newNode_7610_);
                    v___x_7615_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_7616_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2);
                    v___x_7617_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_x_7554_, v_ks_7613_, v_vs_7614_, v___x_7615_, v___x_7616_);
                    crate::leanh::lean_dec_ref(v_vs_7614_);
                    crate::leanh::lean_dec_ref(v_ks_7613_);
                    return v___x_7617_;
                } else {
                    return v_newNode_7610_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_depth_7625_: usize,
    mut v_keys_7626_: *mut crate::leanh::LeanObject,
    mut v_vals_7627_: *mut crate::leanh::LeanObject,
    mut v_i_7628_: *mut crate::leanh::LeanObject,
    mut v_entries_7629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7631_: u8 = 0;
    let mut v_k_7632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7634_: u64 = 0;
    let mut v_h_7635_: usize = 0;
    let mut v___x_7636_: usize = 0;
    let mut v___x_7637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7638_: usize = 0;
    let mut v___x_7639_: usize = 0;
    let mut v___x_7640_: usize = 0;
    let mut v_h_7641_: usize = 0;
    let mut v___x_7642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7630_ = lean_array_get_size(v_keys_7626_);
                v___x_7631_ = lean_nat_dec_lt(v_i_7628_, v___x_7630_);
                if v___x_7631_ == 0 {
                    crate::leanh::lean_dec(v_i_7628_);
                    return v_entries_7629_;
                } else {
                    v_k_7632_ = lean_array_fget_borrowed(v_keys_7626_, v_i_7628_);
                    v_v_7633_ = lean_array_fget_borrowed(v_vals_7627_, v_i_7628_);
                    v___x_7634_ = l_Lean_instHashableMVarId_hash(v_k_7632_);
                    v_h_7635_ = lean_uint64_to_usize(v___x_7634_);
                    v___x_7636_ = 5usize;
                    v___x_7637_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_7638_ = 1usize;
                    v___x_7639_ = lean_usize_sub(v_depth_7625_, v___x_7638_);
                    v___x_7640_ = lean_usize_mul(v___x_7636_, v___x_7639_);
                    v_h_7641_ = lean_usize_shift_right(v_h_7635_, v___x_7640_);
                    v___x_7642_ = lean_nat_add(v_i_7628_, v___x_7637_);
                    crate::leanh::lean_dec(v_i_7628_);
                    crate::leanh::lean_inc(v_v_7633_);
                    crate::leanh::lean_inc(v_k_7632_);
                    v___x_7643_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_entries_7629_, v_h_7641_, v_depth_7625_, v_k_7632_, v_v_7633_);
                    v_i_7628_ = v___x_7642_;
                    v_entries_7629_ = v___x_7643_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_depth_7645_: *mut crate::leanh::LeanObject,
    mut v_keys_7646_: *mut crate::leanh::LeanObject,
    mut v_vals_7647_: *mut crate::leanh::LeanObject,
    mut v_i_7648_: *mut crate::leanh::LeanObject,
    mut v_entries_7649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_7650_: usize = 0;
    let mut v_res_7651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_7650_ = crate::leanh::lean_unbox_usize(v_depth_7645_);
    crate::leanh::lean_dec(v_depth_7645_);
    v_res_7651_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_7650_, v_keys_7646_, v_vals_7647_, v_i_7648_, v_entries_7649_);
    crate::leanh::lean_dec_ref(v_vals_7647_);
    crate::leanh::lean_dec_ref(v_keys_7646_);
    return v_res_7651_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_7652_: *mut crate::leanh::LeanObject,
    mut v_x_7653_: *mut crate::leanh::LeanObject,
    mut v_x_7654_: *mut crate::leanh::LeanObject,
    mut v_x_7655_: *mut crate::leanh::LeanObject,
    mut v_x_7656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2256__boxed_7657_: usize = 0;
    let mut v_x_2257__boxed_7658_: usize = 0;
    let mut v_res_7659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2256__boxed_7657_ = crate::leanh::lean_unbox_usize(v_x_7653_);
    crate::leanh::lean_dec(v_x_7653_);
    v_x_2257__boxed_7658_ = crate::leanh::lean_unbox_usize(v_x_7654_);
    crate::leanh::lean_dec(v_x_7654_);
    v_res_7659_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_7652_, v_x_2256__boxed_7657_, v_x_2257__boxed_7658_, v_x_7655_, v_x_7656_);
    return v_res_7659_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(
    mut v_x_7660_: *mut crate::leanh::LeanObject,
    mut v_x_7661_: *mut crate::leanh::LeanObject,
    mut v_x_7662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7663_: u64 = 0;
    let mut v___x_7664_: usize = 0;
    let mut v___x_7665_: usize = 0;
    let mut v___x_7666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7663_ = l_Lean_instHashableMVarId_hash(v_x_7661_);
    v___x_7664_ = lean_uint64_to_usize(v___x_7663_);
    v___x_7665_ = 1usize;
    v___x_7666_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_7660_, v___x_7664_, v___x_7665_, v_x_7661_, v_x_7662_);
    return v___x_7666_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(
    mut v_mvarId_7667_: *mut crate::leanh::LeanObject,
    mut v_val_7668_: *mut crate::leanh::LeanObject,
    mut v___y_7669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_7672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_7674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_7675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_7676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7679_: u8 = 0;
    let mut v_depth_7680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_7681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_7682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_7683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_7684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_7685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_7686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_7687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_7688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_7689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7692_: u8 = 0;
    let mut v___x_7693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7703_: u8 = 0;
    let mut v_isSharedCheck_7704_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7671_ = lean_st_ref_take(v___y_7669_);
                v_mctx_7672_ = crate::leanh::lean_ctor_get(v___x_7671_, 0);
                v_cache_7673_ = crate::leanh::lean_ctor_get(v___x_7671_, 1);
                v_zetaDeltaFVarIds_7674_ = crate::leanh::lean_ctor_get(v___x_7671_, 2);
                v_postponed_7675_ = crate::leanh::lean_ctor_get(v___x_7671_, 3);
                v_diag_7676_ = crate::leanh::lean_ctor_get(v___x_7671_, 4);
                v_isSharedCheck_7704_ = (!crate::leanh::lean_is_exclusive(v___x_7671_)) as u8;
                if v_isSharedCheck_7704_ == 0 {
                    v___x_7678_ = v___x_7671_;
                    v_isShared_7679_ = v_isSharedCheck_7704_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_7676_);
                    crate::leanh::lean_inc(v_postponed_7675_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_7674_);
                    crate::leanh::lean_inc(v_cache_7673_);
                    crate::leanh::lean_inc(v_mctx_7672_);
                    crate::leanh::lean_dec(v___x_7671_);
                    v___x_7678_ = crate::leanh::lean_box(0);
                    v_isShared_7679_ = v_isSharedCheck_7704_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_7680_ = crate::leanh::lean_ctor_get(v_mctx_7672_, 0);
                v_levelAssignDepth_7681_ = crate::leanh::lean_ctor_get(v_mctx_7672_, 1);
                v_lmvarCounter_7682_ = crate::leanh::lean_ctor_get(v_mctx_7672_, 2);
                v_mvarCounter_7683_ = crate::leanh::lean_ctor_get(v_mctx_7672_, 3);
                v_lDecls_7684_ = crate::leanh::lean_ctor_get(v_mctx_7672_, 4);
                v_decls_7685_ = crate::leanh::lean_ctor_get(v_mctx_7672_, 5);
                v_userNames_7686_ = crate::leanh::lean_ctor_get(v_mctx_7672_, 6);
                v_lAssignment_7687_ = crate::leanh::lean_ctor_get(v_mctx_7672_, 7);
                v_eAssignment_7688_ = crate::leanh::lean_ctor_get(v_mctx_7672_, 8);
                v_dAssignment_7689_ = crate::leanh::lean_ctor_get(v_mctx_7672_, 9);
                v_isSharedCheck_7703_ = (!crate::leanh::lean_is_exclusive(v_mctx_7672_)) as u8;
                if v_isSharedCheck_7703_ == 0 {
                    v___x_7691_ = v_mctx_7672_;
                    v_isShared_7692_ = v_isSharedCheck_7703_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_7689_);
                    crate::leanh::lean_inc(v_eAssignment_7688_);
                    crate::leanh::lean_inc(v_lAssignment_7687_);
                    crate::leanh::lean_inc(v_userNames_7686_);
                    crate::leanh::lean_inc(v_decls_7685_);
                    crate::leanh::lean_inc(v_lDecls_7684_);
                    crate::leanh::lean_inc(v_mvarCounter_7683_);
                    crate::leanh::lean_inc(v_lmvarCounter_7682_);
                    crate::leanh::lean_inc(v_levelAssignDepth_7681_);
                    crate::leanh::lean_inc(v_depth_7680_);
                    crate::leanh::lean_dec(v_mctx_7672_);
                    v___x_7691_ = crate::leanh::lean_box(0);
                    v_isShared_7692_ = v_isSharedCheck_7703_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7693_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(v_eAssignment_7688_, v_mvarId_7667_, v_val_7668_);
                if v_isShared_7692_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7691_, 8, v___x_7693_);
                    v___x_7695_ = v___x_7691_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7702_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7702_, 0, v_depth_7680_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_7702_,
                        1,
                        v_levelAssignDepth_7681_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7702_, 2, v_lmvarCounter_7682_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7702_, 3, v_mvarCounter_7683_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7702_, 4, v_lDecls_7684_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7702_, 5, v_decls_7685_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7702_, 6, v_userNames_7686_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7702_, 7, v_lAssignment_7687_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7702_, 8, v___x_7693_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7702_, 9, v_dAssignment_7689_);
                    v___x_7695_ = v_reuseFailAlloc_7702_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_7679_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7678_, 0, v___x_7695_);
                    v___x_7697_ = v___x_7678_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7701_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7701_, 0, v___x_7695_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7701_, 1, v_cache_7673_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_7701_,
                        2,
                        v_zetaDeltaFVarIds_7674_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7701_, 3, v_postponed_7675_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7701_, 4, v_diag_7676_);
                    v___x_7697_ = v_reuseFailAlloc_7701_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7698_ = lean_st_ref_set(v___y_7669_, v___x_7697_);
                v___x_7699_ = crate::leanh::lean_box(0);
                v___x_7700_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7700_, 0, v___x_7699_);
                return v___x_7700_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg___boxed(
    mut v_mvarId_7705_: *mut crate::leanh::LeanObject,
    mut v_val_7706_: *mut crate::leanh::LeanObject,
    mut v___y_7707_: *mut crate::leanh::LeanObject,
    mut v___y_7708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7709_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(
        v_mvarId_7705_,
        v_val_7706_,
        v___y_7707_,
    );
    crate::leanh::lean_dec(v___y_7707_);
    return v_res_7709_;
}
pub unsafe fn l_Lean_Meta_Sym_preprocessMVar(
    mut v_mvarId_7710_: *mut crate::leanh::LeanObject,
    mut v_a_7711_: *mut crate::leanh::LeanObject,
    mut v_a_7712_: *mut crate::leanh::LeanObject,
    mut v_a_7713_: *mut crate::leanh::LeanObject,
    mut v_a_7714_: *mut crate::leanh::LeanObject,
    mut v_a_7715_: *mut crate::leanh::LeanObject,
    mut v_a_7716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_7720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_7721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_7723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7728_: u8 = 0;
    let mut v___x_7729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7735_: u8 = 0;
    let mut v___x_7736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7740_: u8 = 0;
    let mut v_unused_7741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7745_: u8 = 0;
    let mut v___x_7747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7749_: u8 = 0;
    let mut v_a_7750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7753_: u8 = 0;
    let mut v___x_7755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7757_: u8 = 0;
    let mut v_a_7758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7761_: u8 = 0;
    let mut v___x_7763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7765_: u8 = 0;
    let mut v_a_7766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7769_: u8 = 0;
    let mut v___x_7771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7773_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_7710_);
                v___x_7718_ = l_Lean_MVarId_getDecl(
                    v_mvarId_7710_,
                    v_a_7713_,
                    v_a_7714_,
                    v_a_7715_,
                    v_a_7716_,
                );
                if crate::leanh::lean_obj_tag(v___x_7718_) == 0 {
                    v_a_7719_ = crate::leanh::lean_ctor_get(v___x_7718_, 0);
                    crate::leanh::lean_inc(v_a_7719_);
                    crate::leanh::lean_dec_ref_known(v___x_7718_, 1);
                    v_userName_7720_ = crate::leanh::lean_ctor_get(v_a_7719_, 0);
                    crate::leanh::lean_inc(v_userName_7720_);
                    v_lctx_7721_ = crate::leanh::lean_ctor_get(v_a_7719_, 1);
                    crate::leanh::lean_inc_ref(v_lctx_7721_);
                    v_type_7722_ = crate::leanh::lean_ctor_get(v_a_7719_, 2);
                    crate::leanh::lean_inc_ref(v_type_7722_);
                    v_localInstances_7723_ = crate::leanh::lean_ctor_get(v_a_7719_, 4);
                    crate::leanh::lean_inc_ref(v_localInstances_7723_);
                    crate::leanh::lean_dec(v_a_7719_);
                    v___x_7724_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(
                        v_lctx_7721_,
                        v_a_7711_,
                        v_a_7712_,
                        v_a_7713_,
                        v_a_7714_,
                        v_a_7715_,
                        v_a_7716_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7724_) == 0 {
                        v_a_7725_ = crate::leanh::lean_ctor_get(v___x_7724_, 0);
                        crate::leanh::lean_inc(v_a_7725_);
                        crate::leanh::lean_dec_ref_known(v___x_7724_, 1);
                        v___x_7726_ =
                            l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(
                                v_type_7722_,
                                v_a_7711_,
                                v_a_7712_,
                                v_a_7713_,
                                v_a_7714_,
                                v_a_7715_,
                                v_a_7716_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_7726_) == 0 {
                            v_a_7727_ = crate::leanh::lean_ctor_get(v___x_7726_, 0);
                            crate::leanh::lean_inc(v_a_7727_);
                            crate::leanh::lean_dec_ref_known(v___x_7726_, 1);
                            v___x_7728_ = 2;
                            v___x_7729_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_7730_ = l_Lean_Meta_mkFreshExprMVarAt(
                                v_a_7725_,
                                v_localInstances_7723_,
                                v_a_7727_,
                                v___x_7728_,
                                v_userName_7720_,
                                v___x_7729_,
                                v_a_7713_,
                                v_a_7714_,
                                v_a_7715_,
                                v_a_7716_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_7730_) == 0 {
                                v_a_7731_ = crate::leanh::lean_ctor_get(v___x_7730_, 0);
                                crate::leanh::lean_inc_n(v_a_7731_, 2);
                                crate::leanh::lean_dec_ref_known(v___x_7730_, 1);
                                v___x_7732_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_7710_, v_a_7731_, v_a_7714_);
                                v_isSharedCheck_7740_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_7732_)) as u8;
                                if v_isSharedCheck_7740_ == 0 {
                                    v_unused_7741_ = crate::leanh::lean_ctor_get(v___x_7732_, 0);
                                    crate::leanh::lean_dec(v_unused_7741_);
                                    v___x_7734_ = v___x_7732_;
                                    v_isShared_7735_ = v_isSharedCheck_7740_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_7732_);
                                    v___x_7734_ = crate::leanh::lean_box(0);
                                    v_isShared_7735_ = v_isSharedCheck_7740_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_mvarId_7710_);
                                v_a_7742_ = crate::leanh::lean_ctor_get(v___x_7730_, 0);
                                v_isSharedCheck_7749_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_7730_)) as u8;
                                if v_isSharedCheck_7749_ == 0 {
                                    v___x_7744_ = v___x_7730_;
                                    v_isShared_7745_ = v_isSharedCheck_7749_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_7742_);
                                    crate::leanh::lean_dec(v___x_7730_);
                                    v___x_7744_ = crate::leanh::lean_box(0);
                                    v_isShared_7745_ = v_isSharedCheck_7749_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_7725_);
                            crate::leanh::lean_dec_ref(v_localInstances_7723_);
                            crate::leanh::lean_dec(v_userName_7720_);
                            crate::leanh::lean_dec(v_mvarId_7710_);
                            v_a_7750_ = crate::leanh::lean_ctor_get(v___x_7726_, 0);
                            v_isSharedCheck_7757_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7726_)) as u8;
                            if v_isSharedCheck_7757_ == 0 {
                                v___x_7752_ = v___x_7726_;
                                v_isShared_7753_ = v_isSharedCheck_7757_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7750_);
                                crate::leanh::lean_dec(v___x_7726_);
                                v___x_7752_ = crate::leanh::lean_box(0);
                                v_isShared_7753_ = v_isSharedCheck_7757_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_localInstances_7723_);
                        crate::leanh::lean_dec_ref(v_type_7722_);
                        crate::leanh::lean_dec(v_userName_7720_);
                        crate::leanh::lean_dec(v_mvarId_7710_);
                        v_a_7758_ = crate::leanh::lean_ctor_get(v___x_7724_, 0);
                        v_isSharedCheck_7765_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7724_)) as u8;
                        if v_isSharedCheck_7765_ == 0 {
                            v___x_7760_ = v___x_7724_;
                            v_isShared_7761_ = v_isSharedCheck_7765_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7758_);
                            crate::leanh::lean_dec(v___x_7724_);
                            v___x_7760_ = crate::leanh::lean_box(0);
                            v_isShared_7761_ = v_isSharedCheck_7765_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_7710_);
                    v_a_7766_ = crate::leanh::lean_ctor_get(v___x_7718_, 0);
                    v_isSharedCheck_7773_ = (!crate::leanh::lean_is_exclusive(v___x_7718_)) as u8;
                    if v_isSharedCheck_7773_ == 0 {
                        v___x_7768_ = v___x_7718_;
                        v_isShared_7769_ = v_isSharedCheck_7773_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7766_);
                        crate::leanh::lean_dec(v___x_7718_);
                        v___x_7768_ = crate::leanh::lean_box(0);
                        v_isShared_7769_ = v_isSharedCheck_7773_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7736_ = l_Lean_Expr_mvarId_x21(v_a_7731_);
                crate::leanh::lean_dec(v_a_7731_);
                if v_isShared_7735_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7734_, 0, v___x_7736_);
                    v___x_7738_ = v___x_7734_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7739_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7739_, 0, v___x_7736_);
                    v___x_7738_ = v_reuseFailAlloc_7739_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7738_;
            }
            3 => {
                if v_isShared_7745_ == 0 {
                    v___x_7747_ = v___x_7744_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7748_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7748_, 0, v_a_7742_);
                    v___x_7747_ = v_reuseFailAlloc_7748_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7747_;
            }
            5 => {
                if v_isShared_7753_ == 0 {
                    v___x_7755_ = v___x_7752_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7756_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7756_, 0, v_a_7750_);
                    v___x_7755_ = v_reuseFailAlloc_7756_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7755_;
            }
            7 => {
                if v_isShared_7761_ == 0 {
                    v___x_7763_ = v___x_7760_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7764_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7764_, 0, v_a_7758_);
                    v___x_7763_ = v_reuseFailAlloc_7764_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7763_;
            }
            9 => {
                if v_isShared_7769_ == 0 {
                    v___x_7771_ = v___x_7768_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7772_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7772_, 0, v_a_7766_);
                    v___x_7771_ = v_reuseFailAlloc_7772_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7771_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_preprocessMVar___boxed(
    mut v_mvarId_7774_: *mut crate::leanh::LeanObject,
    mut v_a_7775_: *mut crate::leanh::LeanObject,
    mut v_a_7776_: *mut crate::leanh::LeanObject,
    mut v_a_7777_: *mut crate::leanh::LeanObject,
    mut v_a_7778_: *mut crate::leanh::LeanObject,
    mut v_a_7779_: *mut crate::leanh::LeanObject,
    mut v_a_7780_: *mut crate::leanh::LeanObject,
    mut v_a_7781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7782_ = l_Lean_Meta_Sym_preprocessMVar(
        v_mvarId_7774_,
        v_a_7775_,
        v_a_7776_,
        v_a_7777_,
        v_a_7778_,
        v_a_7779_,
        v_a_7780_,
    );
    crate::leanh::lean_dec(v_a_7780_);
    crate::leanh::lean_dec_ref(v_a_7779_);
    crate::leanh::lean_dec(v_a_7778_);
    crate::leanh::lean_dec_ref(v_a_7777_);
    crate::leanh::lean_dec(v_a_7776_);
    crate::leanh::lean_dec_ref(v_a_7775_);
    return v_res_7782_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0(
    mut v_mvarId_7783_: *mut crate::leanh::LeanObject,
    mut v_val_7784_: *mut crate::leanh::LeanObject,
    mut v___y_7785_: *mut crate::leanh::LeanObject,
    mut v___y_7786_: *mut crate::leanh::LeanObject,
    mut v___y_7787_: *mut crate::leanh::LeanObject,
    mut v___y_7788_: *mut crate::leanh::LeanObject,
    mut v___y_7789_: *mut crate::leanh::LeanObject,
    mut v___y_7790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7792_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(
        v_mvarId_7783_,
        v_val_7784_,
        v___y_7788_,
    );
    return v___x_7792_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___boxed(
    mut v_mvarId_7793_: *mut crate::leanh::LeanObject,
    mut v_val_7794_: *mut crate::leanh::LeanObject,
    mut v___y_7795_: *mut crate::leanh::LeanObject,
    mut v___y_7796_: *mut crate::leanh::LeanObject,
    mut v___y_7797_: *mut crate::leanh::LeanObject,
    mut v___y_7798_: *mut crate::leanh::LeanObject,
    mut v___y_7799_: *mut crate::leanh::LeanObject,
    mut v___y_7800_: *mut crate::leanh::LeanObject,
    mut v___y_7801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7802_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0(
        v_mvarId_7793_,
        v_val_7794_,
        v___y_7795_,
        v___y_7796_,
        v___y_7797_,
        v___y_7798_,
        v___y_7799_,
        v___y_7800_,
    );
    crate::leanh::lean_dec(v___y_7800_);
    crate::leanh::lean_dec_ref(v___y_7799_);
    crate::leanh::lean_dec(v___y_7798_);
    crate::leanh::lean_dec_ref(v___y_7797_);
    crate::leanh::lean_dec(v___y_7796_);
    crate::leanh::lean_dec_ref(v___y_7795_);
    return v_res_7802_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0(
    mut v_00_u03b2_7803_: *mut crate::leanh::LeanObject,
    mut v_x_7804_: *mut crate::leanh::LeanObject,
    mut v_x_7805_: *mut crate::leanh::LeanObject,
    mut v_x_7806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7807_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(v_x_7804_, v_x_7805_, v_x_7806_);
    return v___x_7807_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1(
    mut v_00_u03b2_7808_: *mut crate::leanh::LeanObject,
    mut v_x_7809_: *mut crate::leanh::LeanObject,
    mut v_x_7810_: usize,
    mut v_x_7811_: usize,
    mut v_x_7812_: *mut crate::leanh::LeanObject,
    mut v_x_7813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7814_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_7809_, v_x_7810_, v_x_7811_, v_x_7812_, v_x_7813_);
    return v___x_7814_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_7815_: *mut crate::leanh::LeanObject,
    mut v_x_7816_: *mut crate::leanh::LeanObject,
    mut v_x_7817_: *mut crate::leanh::LeanObject,
    mut v_x_7818_: *mut crate::leanh::LeanObject,
    mut v_x_7819_: *mut crate::leanh::LeanObject,
    mut v_x_7820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2610__boxed_7821_: usize = 0;
    let mut v_x_2611__boxed_7822_: usize = 0;
    let mut v_res_7823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2610__boxed_7821_ = crate::leanh::lean_unbox_usize(v_x_7817_);
    crate::leanh::lean_dec(v_x_7817_);
    v_x_2611__boxed_7822_ = crate::leanh::lean_unbox_usize(v_x_7818_);
    crate::leanh::lean_dec(v_x_7818_);
    v_res_7823_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1(v_00_u03b2_7815_, v_x_7816_, v_x_2610__boxed_7821_, v_x_2611__boxed_7822_, v_x_7819_, v_x_7820_);
    return v_res_7823_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_7824_: *mut crate::leanh::LeanObject,
    mut v_n_7825_: *mut crate::leanh::LeanObject,
    mut v_k_7826_: *mut crate::leanh::LeanObject,
    mut v_v_7827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7828_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(v_n_7825_, v_k_7826_, v_v_7827_);
    return v___x_7828_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_7829_: *mut crate::leanh::LeanObject,
    mut v_depth_7830_: usize,
    mut v_keys_7831_: *mut crate::leanh::LeanObject,
    mut v_vals_7832_: *mut crate::leanh::LeanObject,
    mut v_heq_7833_: *mut crate::leanh::LeanObject,
    mut v_i_7834_: *mut crate::leanh::LeanObject,
    mut v_entries_7835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7836_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_7830_, v_keys_7831_, v_vals_7832_, v_i_7834_, v_entries_7835_);
    return v___x_7836_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_7837_: *mut crate::leanh::LeanObject,
    mut v_depth_7838_: *mut crate::leanh::LeanObject,
    mut v_keys_7839_: *mut crate::leanh::LeanObject,
    mut v_vals_7840_: *mut crate::leanh::LeanObject,
    mut v_heq_7841_: *mut crate::leanh::LeanObject,
    mut v_i_7842_: *mut crate::leanh::LeanObject,
    mut v_entries_7843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_7844_: usize = 0;
    let mut v_res_7845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_7844_ = crate::leanh::lean_unbox_usize(v_depth_7838_);
    crate::leanh::lean_dec(v_depth_7838_);
    v_res_7845_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_7837_, v_depth_boxed_7844_, v_keys_7839_, v_vals_7840_, v_heq_7841_, v_i_7842_, v_entries_7843_);
    crate::leanh::lean_dec_ref(v_vals_7840_);
    crate::leanh::lean_dec_ref(v_keys_7839_);
    return v_res_7845_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_7846_: *mut crate::leanh::LeanObject,
    mut v_x_7847_: *mut crate::leanh::LeanObject,
    mut v_x_7848_: *mut crate::leanh::LeanObject,
    mut v_x_7849_: *mut crate::leanh::LeanObject,
    mut v_x_7850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7851_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_7847_, v_x_7848_, v_x_7849_, v_x_7850_);
    return v___x_7851_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(
    mut v_msg_7852_: *mut crate::leanh::LeanObject,
    mut v___y_7853_: *mut crate::leanh::LeanObject,
    mut v___y_7854_: *mut crate::leanh::LeanObject,
    mut v___y_7855_: *mut crate::leanh::LeanObject,
    mut v___y_7856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_7858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7863_: u8 = 0;
    let mut v___x_7864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7868_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_7858_ = crate::leanh::lean_ctor_get(v___y_7855_, 5);
                v___x_7859_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_7852_, v___y_7853_, v___y_7854_, v___y_7855_, v___y_7856_);
                v_a_7860_ = crate::leanh::lean_ctor_get(v___x_7859_, 0);
                v_isSharedCheck_7868_ = (!crate::leanh::lean_is_exclusive(v___x_7859_)) as u8;
                if v_isSharedCheck_7868_ == 0 {
                    v___x_7862_ = v___x_7859_;
                    v_isShared_7863_ = v_isSharedCheck_7868_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_7860_);
                    crate::leanh::lean_dec(v___x_7859_);
                    v___x_7862_ = crate::leanh::lean_box(0);
                    v_isShared_7863_ = v_isSharedCheck_7868_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_7858_);
                v___x_7864_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7864_, 0, v_ref_7858_);
                crate::leanh::lean_ctor_set(v___x_7864_, 1, v_a_7860_);
                if v_isShared_7863_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7862_, 1);
                    crate::leanh::lean_ctor_set(v___x_7862_, 0, v___x_7864_);
                    v___x_7866_ = v___x_7862_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7867_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7867_, 0, v___x_7864_);
                    v___x_7866_ = v_reuseFailAlloc_7867_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7866_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg___boxed(
    mut v_msg_7869_: *mut crate::leanh::LeanObject,
    mut v___y_7870_: *mut crate::leanh::LeanObject,
    mut v___y_7871_: *mut crate::leanh::LeanObject,
    mut v___y_7872_: *mut crate::leanh::LeanObject,
    mut v___y_7873_: *mut crate::leanh::LeanObject,
    mut v___y_7874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7875_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v_msg_7869_, v___y_7870_, v___y_7871_, v___y_7872_, v___y_7873_);
    crate::leanh::lean_dec(v___y_7873_);
    crate::leanh::lean_dec_ref(v___y_7872_);
    crate::leanh::lean_dec(v___y_7871_);
    crate::leanh::lean_dec_ref(v___y_7870_);
    return v_res_7875_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7877_ =
        l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__0;
    v___x_7878_ = l_Lean_stringToMessageData(v___x_7877_);
    return v___x_7878_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(
    mut v_msg_7881_: *mut crate::leanh::LeanObject,
    mut v_e_7882_: *mut crate::leanh::LeanObject,
    mut v_a_7883_: *mut crate::leanh::LeanObject,
    mut v_a_7884_: *mut crate::leanh::LeanObject,
    mut v_a_7885_: *mut crate::leanh::LeanObject,
    mut v_a_7886_: *mut crate::leanh::LeanObject,
    mut v_a_7887_: *mut crate::leanh::LeanObject,
    mut v_a_7888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_7891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7899_: u8 = 0;
    let mut v___x_7900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7898_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1;
                v___x_7899_ = lean_string_dec_eq(v_msg_7881_, v___x_7898_);
                if v___x_7899_ == 0 {
                    v___x_7900_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__2;
                    v___x_7901_ = lean_string_append(v___x_7900_, v_msg_7881_);
                    crate::leanh::lean_dec_ref(v_msg_7881_);
                    v___x_7902_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__3;
                    v___x_7903_ = lean_string_append(v___x_7901_, v___x_7902_);
                    v___y_7891_ = v___x_7903_;
                    state = 1;
                    continue;
                } else {
                    v___y_7891_ = v_msg_7881_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7892_ = l_Lean_stringToMessageData(v___y_7891_);
                v___x_7893_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1_once), _init_l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1);
                v___x_7894_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7894_, 0, v___x_7892_);
                crate::leanh::lean_ctor_set(v___x_7894_, 1, v___x_7893_);
                v___x_7895_ = l_Lean_indentExpr(v_e_7882_);
                v___x_7896_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7896_, 0, v___x_7894_);
                crate::leanh::lean_ctor_set(v___x_7896_, 1, v___x_7895_);
                v___x_7897_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v___x_7896_, v_a_7885_, v_a_7886_, v_a_7887_, v_a_7888_);
                return v___x_7897_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___boxed(
    mut v_msg_7904_: *mut crate::leanh::LeanObject,
    mut v_e_7905_: *mut crate::leanh::LeanObject,
    mut v_a_7906_: *mut crate::leanh::LeanObject,
    mut v_a_7907_: *mut crate::leanh::LeanObject,
    mut v_a_7908_: *mut crate::leanh::LeanObject,
    mut v_a_7909_: *mut crate::leanh::LeanObject,
    mut v_a_7910_: *mut crate::leanh::LeanObject,
    mut v_a_7911_: *mut crate::leanh::LeanObject,
    mut v_a_7912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7913_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(
        v_msg_7904_,
        v_e_7905_,
        v_a_7906_,
        v_a_7907_,
        v_a_7908_,
        v_a_7909_,
        v_a_7910_,
        v_a_7911_,
    );
    crate::leanh::lean_dec(v_a_7911_);
    crate::leanh::lean_dec_ref(v_a_7910_);
    crate::leanh::lean_dec(v_a_7909_);
    crate::leanh::lean_dec_ref(v_a_7908_);
    crate::leanh::lean_dec(v_a_7907_);
    crate::leanh::lean_dec_ref(v_a_7906_);
    return v_res_7913_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0(
    mut v_00_u03b1_7914_: *mut crate::leanh::LeanObject,
    mut v_msg_7915_: *mut crate::leanh::LeanObject,
    mut v___y_7916_: *mut crate::leanh::LeanObject,
    mut v___y_7917_: *mut crate::leanh::LeanObject,
    mut v___y_7918_: *mut crate::leanh::LeanObject,
    mut v___y_7919_: *mut crate::leanh::LeanObject,
    mut v___y_7920_: *mut crate::leanh::LeanObject,
    mut v___y_7921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7923_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v_msg_7915_, v___y_7918_, v___y_7919_, v___y_7920_, v___y_7921_);
    return v___x_7923_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___boxed(
    mut v_00_u03b1_7924_: *mut crate::leanh::LeanObject,
    mut v_msg_7925_: *mut crate::leanh::LeanObject,
    mut v___y_7926_: *mut crate::leanh::LeanObject,
    mut v___y_7927_: *mut crate::leanh::LeanObject,
    mut v___y_7928_: *mut crate::leanh::LeanObject,
    mut v___y_7929_: *mut crate::leanh::LeanObject,
    mut v___y_7930_: *mut crate::leanh::LeanObject,
    mut v___y_7931_: *mut crate::leanh::LeanObject,
    mut v___y_7932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7933_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0(v_00_u03b1_7924_, v_msg_7925_, v___y_7926_, v___y_7927_, v___y_7928_, v___y_7929_, v___y_7930_, v___y_7931_);
    crate::leanh::lean_dec(v___y_7931_);
    crate::leanh::lean_dec_ref(v___y_7930_);
    crate::leanh::lean_dec(v___y_7929_);
    crate::leanh::lean_dec_ref(v___y_7928_);
    crate::leanh::lean_dec(v___y_7927_);
    crate::leanh::lean_dec_ref(v___y_7926_);
    return v_res_7933_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(
    mut v_keys_7934_: *mut crate::leanh::LeanObject,
    mut v_vals_7935_: *mut crate::leanh::LeanObject,
    mut v_i_7936_: *mut crate::leanh::LeanObject,
    mut v_k_7937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7939_: u8 = 0;
    let mut v___x_7940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_7941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7942_: u8 = 0;
    let mut v___x_7943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7938_ = lean_array_get_size(v_keys_7934_);
                v___x_7939_ = lean_nat_dec_lt(v_i_7936_, v___x_7938_);
                if v___x_7939_ == 0 {
                    crate::leanh::lean_dec_ref(v_k_7937_);
                    crate::leanh::lean_dec(v_i_7936_);
                    v___x_7940_ = crate::leanh::lean_box(0);
                    return v___x_7940_;
                } else {
                    v_k_x27_7941_ = lean_array_fget_borrowed(v_keys_7934_, v_i_7936_);
                    crate::leanh::lean_inc(v_k_x27_7941_);
                    crate::leanh::lean_inc_ref(v_k_7937_);
                    v___x_7942_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
                            v_k_7937_,
                            v_k_x27_7941_,
                        );
                    if v___x_7942_ == 0 {
                        v___x_7943_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_7944_ = lean_nat_add(v_i_7936_, v___x_7943_);
                        crate::leanh::lean_dec(v_i_7936_);
                        v_i_7936_ = v___x_7944_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_7937_);
                        v___x_7946_ = lean_array_fget_borrowed(v_vals_7935_, v_i_7936_);
                        crate::leanh::lean_dec(v_i_7936_);
                        crate::leanh::lean_inc(v___x_7946_);
                        crate::leanh::lean_inc(v_k_x27_7941_);
                        v___x_7947_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7947_, 0, v_k_x27_7941_);
                        crate::leanh::lean_ctor_set(v___x_7947_, 1, v___x_7946_);
                        v___x_7948_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7948_, 0, v___x_7947_);
                        return v___x_7948_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_7949_: *mut crate::leanh::LeanObject,
    mut v_vals_7950_: *mut crate::leanh::LeanObject,
    mut v_i_7951_: *mut crate::leanh::LeanObject,
    mut v_k_7952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7953_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_keys_7949_, v_vals_7950_, v_i_7951_, v_k_7952_);
    crate::leanh::lean_dec_ref(v_vals_7950_);
    crate::leanh::lean_dec_ref(v_keys_7949_);
    return v_res_7953_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(
    mut v_x_7954_: *mut crate::leanh::LeanObject,
    mut v_x_7955_: usize,
    mut v_x_7956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_7957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7959_: usize = 0;
    let mut v___x_7960_: usize = 0;
    let mut v___x_7961_: usize = 0;
    let mut v_j_7962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_7964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7966_: u8 = 0;
    let mut v___x_7967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_7970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7971_: usize = 0;
    let mut v___x_7973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_7974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_7975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_7954_) == 0 {
                    v_es_7957_ = crate::leanh::lean_ctor_get(v_x_7954_, 0);
                    crate::leanh::lean_inc_ref(v_es_7957_);
                    crate::leanh::lean_dec_ref_known(v_x_7954_, 1);
                    v___x_7958_ = crate::leanh::lean_box(2);
                    v___x_7959_ = 5usize;
                    v___x_7960_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1);
                    v___x_7961_ = lean_usize_land(v_x_7955_, v___x_7960_);
                    v_j_7962_ = lean_usize_to_nat(v___x_7961_);
                    v___x_7963_ = lean_array_get(v___x_7958_, v_es_7957_, v_j_7962_);
                    crate::leanh::lean_dec(v_j_7962_);
                    crate::leanh::lean_dec_ref(v_es_7957_);
                    match crate::leanh::lean_obj_tag(v___x_7963_) {
                        0 => {
                            v_key_7964_ = crate::leanh::lean_ctor_get(v___x_7963_, 0);
                            crate::leanh::lean_inc_n(v_key_7964_, 2);
                            v_val_7965_ = crate::leanh::lean_ctor_get(v___x_7963_, 1);
                            crate::leanh::lean_inc(v_val_7965_);
                            crate::leanh::lean_dec_ref_known(v___x_7963_, 2);
                            v___x_7966_ =
                                l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
                                    v_x_7956_,
                                    v_key_7964_,
                                );
                            if v___x_7966_ == 0 {
                                crate::leanh::lean_dec(v_val_7965_);
                                crate::leanh::lean_dec(v_key_7964_);
                                v___x_7967_ = crate::leanh::lean_box(0);
                                return v___x_7967_;
                            } else {
                                v___x_7968_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_7968_, 0, v_key_7964_);
                                crate::leanh::lean_ctor_set(v___x_7968_, 1, v_val_7965_);
                                v___x_7969_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_7969_, 0, v___x_7968_);
                                return v___x_7969_;
                            }
                        }
                        1 => {
                            v_node_7970_ = crate::leanh::lean_ctor_get(v___x_7963_, 0);
                            crate::leanh::lean_inc(v_node_7970_);
                            crate::leanh::lean_dec_ref_known(v___x_7963_, 1);
                            v___x_7971_ = lean_usize_shift_right(v_x_7955_, v___x_7959_);
                            v_x_7954_ = v_node_7970_;
                            v_x_7955_ = v___x_7971_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            crate::leanh::lean_dec_ref(v_x_7956_);
                            v___x_7973_ = crate::leanh::lean_box(0);
                            return v___x_7973_;
                        }
                    }
                } else {
                    v_ks_7974_ = crate::leanh::lean_ctor_get(v_x_7954_, 0);
                    crate::leanh::lean_inc_ref(v_ks_7974_);
                    v_vs_7975_ = crate::leanh::lean_ctor_get(v_x_7954_, 1);
                    crate::leanh::lean_inc_ref(v_vs_7975_);
                    crate::leanh::lean_dec_ref_known(v_x_7954_, 2);
                    v___x_7976_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_7977_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_ks_7974_, v_vs_7975_, v___x_7976_, v_x_7956_);
                    crate::leanh::lean_dec_ref(v_vs_7975_);
                    crate::leanh::lean_dec_ref(v_ks_7974_);
                    return v___x_7977_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg___boxed(
    mut v_x_7978_: *mut crate::leanh::LeanObject,
    mut v_x_7979_: *mut crate::leanh::LeanObject,
    mut v_x_7980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_7444__boxed_7981_: usize = 0;
    let mut v_res_7982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_7444__boxed_7981_ = crate::leanh::lean_unbox_usize(v_x_7979_);
    crate::leanh::lean_dec(v_x_7979_);
    v_res_7982_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_7978_, v_x_7444__boxed_7981_, v_x_7980_);
    return v_res_7982_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(
    mut v_x_7983_: *mut crate::leanh::LeanObject,
    mut v_x_7984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7985_: u64 = 0;
    let mut v___x_7986_: usize = 0;
    let mut v___x_7987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7985_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_7984_);
    v___x_7986_ = lean_uint64_to_usize(v___x_7985_);
    crate::leanh::lean_inc_ref(v_x_7983_);
    v___x_7987_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_7983_, v___x_7986_, v_x_7984_);
    return v___x_7987_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg___boxed(
    mut v_x_7988_: *mut crate::leanh::LeanObject,
    mut v_x_7989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7990_ =
        l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(
            v_x_7988_, v_x_7989_,
        );
    crate::leanh::lean_dec_ref(v_x_7988_);
    return v_res_7990_;
}
pub unsafe fn l_Lean_Expr_checkMaxShared___lam__0(
    mut v_msg_7991_: *mut crate::leanh::LeanObject,
    mut v_e_7992_: *mut crate::leanh::LeanObject,
    mut v___y_7993_: *mut crate::leanh::LeanObject,
    mut v___y_7994_: *mut crate::leanh::LeanObject,
    mut v___y_7995_: *mut crate::leanh::LeanObject,
    mut v___y_7996_: *mut crate::leanh::LeanObject,
    mut v___y_7997_: *mut crate::leanh::LeanObject,
    mut v___y_7998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8001_: u8 = 0;
    let mut v___x_8002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8009_: u8 = 0;
    let mut v___x_8011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8013_: u8 = 0;
    let mut v___x_8014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_8015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_8019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8020_: u8 = 0;
    let mut v___x_8021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8014_ = lean_st_ref_get(v___y_7994_);
                v_share_8015_ = crate::leanh::lean_ctor_get(v___x_8014_, 0);
                crate::leanh::lean_inc_ref(v_share_8015_);
                crate::leanh::lean_dec(v___x_8014_);
                crate::leanh::lean_inc_ref(v_e_7992_);
                v___x_8016_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_share_8015_, v_e_7992_);
                crate::leanh::lean_dec_ref(v_share_8015_);
                if crate::leanh::lean_obj_tag(v___x_8016_) == 0 {
                    v___x_8017_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_7991_, v_e_7992_, v___y_7993_, v___y_7994_, v___y_7995_, v___y_7996_, v___y_7997_, v___y_7998_);
                    v___y_8005_ = v___x_8017_;
                    state = 2;
                    continue;
                } else {
                    v_val_8018_ = crate::leanh::lean_ctor_get(v___x_8016_, 0);
                    crate::leanh::lean_inc(v_val_8018_);
                    crate::leanh::lean_dec_ref_known(v___x_8016_, 1);
                    v_fst_8019_ = crate::leanh::lean_ctor_get(v_val_8018_, 0);
                    crate::leanh::lean_inc(v_fst_8019_);
                    crate::leanh::lean_dec(v_val_8018_);
                    v___x_8020_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_fst_8019_,
                            v_e_7992_,
                        );
                    crate::leanh::lean_dec(v_fst_8019_);
                    if v___x_8020_ == 0 {
                        v___x_8021_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_7991_, v_e_7992_, v___y_7993_, v___y_7994_, v___y_7995_, v___y_7996_, v___y_7997_, v___y_7998_);
                        v___y_8005_ = v___x_8021_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_e_7992_);
                        crate::leanh::lean_dec_ref(v_msg_7991_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8001_ = 1;
                v___x_8002_ = crate::leanh::lean_box((v___x_8001_) as usize);
                v___x_8003_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_8003_, 0, v___x_8002_);
                return v___x_8003_;
            }
            2 => {
                v_a_8006_ = crate::leanh::lean_ctor_get(v___y_8005_, 0);
                v_isSharedCheck_8013_ = (!crate::leanh::lean_is_exclusive(v___y_8005_)) as u8;
                if v_isSharedCheck_8013_ == 0 {
                    v___x_8008_ = v___y_8005_;
                    v_isShared_8009_ = v_isSharedCheck_8013_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_8006_);
                    crate::leanh::lean_dec(v___y_8005_);
                    v___x_8008_ = crate::leanh::lean_box(0);
                    v_isShared_8009_ = v_isSharedCheck_8013_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_8009_ == 0 {
                    v___x_8011_ = v___x_8008_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8012_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8012_, 0, v_a_8006_);
                    v___x_8011_ = v_reuseFailAlloc_8012_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8011_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_checkMaxShared___lam__0___boxed(
    mut v_msg_8022_: *mut crate::leanh::LeanObject,
    mut v_e_8023_: *mut crate::leanh::LeanObject,
    mut v___y_8024_: *mut crate::leanh::LeanObject,
    mut v___y_8025_: *mut crate::leanh::LeanObject,
    mut v___y_8026_: *mut crate::leanh::LeanObject,
    mut v___y_8027_: *mut crate::leanh::LeanObject,
    mut v___y_8028_: *mut crate::leanh::LeanObject,
    mut v___y_8029_: *mut crate::leanh::LeanObject,
    mut v___y_8030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8031_ = l_Lean_Expr_checkMaxShared___lam__0(
        v_msg_8022_,
        v_e_8023_,
        v___y_8024_,
        v___y_8025_,
        v___y_8026_,
        v___y_8027_,
        v___y_8028_,
        v___y_8029_,
    );
    crate::leanh::lean_dec(v___y_8029_);
    crate::leanh::lean_dec_ref(v___y_8028_);
    crate::leanh::lean_dec(v___y_8027_);
    crate::leanh::lean_dec_ref(v___y_8026_);
    crate::leanh::lean_dec(v___y_8025_);
    crate::leanh::lean_dec_ref(v___y_8024_);
    return v_res_8031_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(
    mut v_a_8032_: *mut crate::leanh::LeanObject,
    mut v_x_8033_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_8034_: u8 = 0;
    let mut v_key_8035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_8036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8037_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_8033_) == 0 {
                    v___x_8034_ = 0;
                    return v___x_8034_;
                } else {
                    v_key_8035_ = crate::leanh::lean_ctor_get(v_x_8033_, 0);
                    v_tail_8036_ = crate::leanh::lean_ctor_get(v_x_8033_, 2);
                    v___x_8037_ = lean_expr_eqv(v_key_8035_, v_a_8032_);
                    if v___x_8037_ == 0 {
                        v_x_8033_ = v_tail_8036_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_8037_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg___boxed(
    mut v_a_8039_: *mut crate::leanh::LeanObject,
    mut v_x_8040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8041_: u8 = 0;
    let mut v_r_8042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8041_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_8039_, v_x_8040_);
    crate::leanh::lean_dec(v_x_8040_);
    crate::leanh::lean_dec_ref(v_a_8039_);
    v_r_8042_ = crate::leanh::lean_box((v_res_8041_) as usize);
    return v_r_8042_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(
    mut v_a_8043_: *mut crate::leanh::LeanObject,
    mut v_b_8044_: *mut crate::leanh::LeanObject,
    mut v_x_8045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_8046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_8047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_8048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8051_: u8 = 0;
    let mut v___x_8052_: u8 = 0;
    let mut v___x_8053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8060_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_8045_) == 0 {
                    crate::leanh::lean_dec(v_b_8044_);
                    crate::leanh::lean_dec_ref(v_a_8043_);
                    return v_x_8045_;
                } else {
                    v_key_8046_ = crate::leanh::lean_ctor_get(v_x_8045_, 0);
                    v_value_8047_ = crate::leanh::lean_ctor_get(v_x_8045_, 1);
                    v_tail_8048_ = crate::leanh::lean_ctor_get(v_x_8045_, 2);
                    v_isSharedCheck_8060_ = (!crate::leanh::lean_is_exclusive(v_x_8045_)) as u8;
                    if v_isSharedCheck_8060_ == 0 {
                        v___x_8050_ = v_x_8045_;
                        v_isShared_8051_ = v_isSharedCheck_8060_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_8048_);
                        crate::leanh::lean_inc(v_value_8047_);
                        crate::leanh::lean_inc(v_key_8046_);
                        crate::leanh::lean_dec(v_x_8045_);
                        v___x_8050_ = crate::leanh::lean_box(0);
                        v_isShared_8051_ = v_isSharedCheck_8060_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8052_ = lean_expr_eqv(v_key_8046_, v_a_8043_);
                if v___x_8052_ == 0 {
                    v___x_8053_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_8043_, v_b_8044_, v_tail_8048_);
                    if v_isShared_8051_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8050_, 2, v___x_8053_);
                        v___x_8055_ = v___x_8050_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8056_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8056_, 0, v_key_8046_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8056_, 1, v_value_8047_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8056_, 2, v___x_8053_);
                        v___x_8055_ = v_reuseFailAlloc_8056_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_8047_);
                    crate::leanh::lean_dec(v_key_8046_);
                    if v_isShared_8051_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8050_, 1, v_b_8044_);
                        crate::leanh::lean_ctor_set(v___x_8050_, 0, v_a_8043_);
                        v___x_8058_ = v___x_8050_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_8059_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8059_, 0, v_a_8043_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8059_, 1, v_b_8044_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8059_, 2, v_tail_8048_);
                        v___x_8058_ = v_reuseFailAlloc_8059_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_8055_;
            }
            3 => {
                return v___x_8058_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(
    mut v_x_8061_: *mut crate::leanh::LeanObject,
    mut v_x_8062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_8063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_8064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_8065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8068_: u8 = 0;
    let mut v___x_8069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8070_: u64 = 0;
    let mut v___x_8071_: u64 = 0;
    let mut v___x_8072_: u64 = 0;
    let mut v_fold_8073_: u64 = 0;
    let mut v___x_8074_: u64 = 0;
    let mut v___x_8075_: u64 = 0;
    let mut v___x_8076_: u64 = 0;
    let mut v___x_8077_: usize = 0;
    let mut v___x_8078_: usize = 0;
    let mut v___x_8079_: usize = 0;
    let mut v___x_8080_: usize = 0;
    let mut v___x_8081_: usize = 0;
    let mut v___x_8082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8088_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_8062_) == 0 {
                    return v_x_8061_;
                } else {
                    v_key_8063_ = crate::leanh::lean_ctor_get(v_x_8062_, 0);
                    v_value_8064_ = crate::leanh::lean_ctor_get(v_x_8062_, 1);
                    v_tail_8065_ = crate::leanh::lean_ctor_get(v_x_8062_, 2);
                    v_isSharedCheck_8088_ = (!crate::leanh::lean_is_exclusive(v_x_8062_)) as u8;
                    if v_isSharedCheck_8088_ == 0 {
                        v___x_8067_ = v_x_8062_;
                        v_isShared_8068_ = v_isSharedCheck_8088_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_8065_);
                        crate::leanh::lean_inc(v_value_8064_);
                        crate::leanh::lean_inc(v_key_8063_);
                        crate::leanh::lean_dec(v_x_8062_);
                        v___x_8067_ = crate::leanh::lean_box(0);
                        v_isShared_8068_ = v_isSharedCheck_8088_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8069_ = lean_array_get_size(v_x_8061_);
                v___x_8070_ = l_Lean_Expr_hash(v_key_8063_);
                v___x_8071_ = 32u64;
                v___x_8072_ = lean_uint64_shift_right(v___x_8070_, v___x_8071_);
                v_fold_8073_ = lean_uint64_xor(v___x_8070_, v___x_8072_);
                v___x_8074_ = 16u64;
                v___x_8075_ = lean_uint64_shift_right(v_fold_8073_, v___x_8074_);
                v___x_8076_ = lean_uint64_xor(v_fold_8073_, v___x_8075_);
                v___x_8077_ = lean_uint64_to_usize(v___x_8076_);
                v___x_8078_ = lean_usize_of_nat(v___x_8069_);
                v___x_8079_ = 1usize;
                v___x_8080_ = lean_usize_sub(v___x_8078_, v___x_8079_);
                v___x_8081_ = lean_usize_land(v___x_8077_, v___x_8080_);
                v___x_8082_ = lean_array_uget_borrowed(v_x_8061_, v___x_8081_);
                crate::leanh::lean_inc(v___x_8082_);
                if v_isShared_8068_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8067_, 2, v___x_8082_);
                    v___x_8084_ = v___x_8067_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8087_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8087_, 0, v_key_8063_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8087_, 1, v_value_8064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8087_, 2, v___x_8082_);
                    v___x_8084_ = v_reuseFailAlloc_8087_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8085_ = lean_array_uset(v_x_8061_, v___x_8081_, v___x_8084_);
                v_x_8061_ = v___x_8085_;
                v_x_8062_ = v_tail_8065_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(
    mut v_i_8089_: *mut crate::leanh::LeanObject,
    mut v_source_8090_: *mut crate::leanh::LeanObject,
    mut v_target_8091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8093_: u8 = 0;
    let mut v_es_8094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_8096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_8097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8092_ = lean_array_get_size(v_source_8090_);
                v___x_8093_ = lean_nat_dec_lt(v_i_8089_, v___x_8092_);
                if v___x_8093_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_8090_);
                    crate::leanh::lean_dec(v_i_8089_);
                    return v_target_8091_;
                } else {
                    v_es_8094_ = lean_array_fget(v_source_8090_, v_i_8089_);
                    v___x_8095_ = crate::leanh::lean_box(0);
                    v_source_8096_ = lean_array_fset(v_source_8090_, v_i_8089_, v___x_8095_);
                    v_target_8097_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(v_target_8091_, v_es_8094_);
                    v___x_8098_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_8099_ = lean_nat_add(v_i_8089_, v___x_8098_);
                    crate::leanh::lean_dec(v_i_8089_);
                    v_i_8089_ = v___x_8099_;
                    v_source_8090_ = v_source_8096_;
                    v_target_8091_ = v_target_8097_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(
    mut v_data_8101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_8104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8102_ = lean_array_get_size(v_data_8101_);
    v___x_8103_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_8104_ = lean_nat_mul(v___x_8102_, v___x_8103_);
    v___x_8105_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_8106_ = crate::leanh::lean_box(0);
    v___x_8107_ = lean_mk_array(v_nbuckets_8104_, v___x_8106_);
    v___x_8108_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(v___x_8105_, v_data_8101_, v___x_8107_);
    return v___x_8108_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(
    mut v_m_8109_: *mut crate::leanh::LeanObject,
    mut v_a_8110_: *mut crate::leanh::LeanObject,
    mut v_b_8111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_8112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_8113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8116_: u8 = 0;
    let mut v___x_8117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8118_: u64 = 0;
    let mut v___x_8119_: u64 = 0;
    let mut v___x_8120_: u64 = 0;
    let mut v_fold_8121_: u64 = 0;
    let mut v___x_8122_: u64 = 0;
    let mut v___x_8123_: u64 = 0;
    let mut v___x_8124_: u64 = 0;
    let mut v___x_8125_: usize = 0;
    let mut v___x_8126_: usize = 0;
    let mut v___x_8127_: usize = 0;
    let mut v___x_8128_: usize = 0;
    let mut v___x_8129_: usize = 0;
    let mut v_bkt_8130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8131_: u8 = 0;
    let mut v___x_8132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_8133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_8135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8141_: u8 = 0;
    let mut v_val_8142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_8150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8156_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_8112_ = crate::leanh::lean_ctor_get(v_m_8109_, 0);
                v_buckets_8113_ = crate::leanh::lean_ctor_get(v_m_8109_, 1);
                v_isSharedCheck_8156_ = (!crate::leanh::lean_is_exclusive(v_m_8109_)) as u8;
                if v_isSharedCheck_8156_ == 0 {
                    v___x_8115_ = v_m_8109_;
                    v_isShared_8116_ = v_isSharedCheck_8156_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_8113_);
                    crate::leanh::lean_inc(v_size_8112_);
                    crate::leanh::lean_dec(v_m_8109_);
                    v___x_8115_ = crate::leanh::lean_box(0);
                    v_isShared_8116_ = v_isSharedCheck_8156_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8117_ = lean_array_get_size(v_buckets_8113_);
                v___x_8118_ = l_Lean_Expr_hash(v_a_8110_);
                v___x_8119_ = 32u64;
                v___x_8120_ = lean_uint64_shift_right(v___x_8118_, v___x_8119_);
                v_fold_8121_ = lean_uint64_xor(v___x_8118_, v___x_8120_);
                v___x_8122_ = 16u64;
                v___x_8123_ = lean_uint64_shift_right(v_fold_8121_, v___x_8122_);
                v___x_8124_ = lean_uint64_xor(v_fold_8121_, v___x_8123_);
                v___x_8125_ = lean_uint64_to_usize(v___x_8124_);
                v___x_8126_ = lean_usize_of_nat(v___x_8117_);
                v___x_8127_ = 1usize;
                v___x_8128_ = lean_usize_sub(v___x_8126_, v___x_8127_);
                v___x_8129_ = lean_usize_land(v___x_8125_, v___x_8128_);
                v_bkt_8130_ = lean_array_uget_borrowed(v_buckets_8113_, v___x_8129_);
                v___x_8131_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_8110_, v_bkt_8130_);
                if v___x_8131_ == 0 {
                    v___x_8132_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_8133_ = lean_nat_add(v_size_8112_, v___x_8132_);
                    crate::leanh::lean_dec(v_size_8112_);
                    crate::leanh::lean_inc(v_bkt_8130_);
                    v___x_8134_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_8134_, 0, v_a_8110_);
                    crate::leanh::lean_ctor_set(v___x_8134_, 1, v_b_8111_);
                    crate::leanh::lean_ctor_set(v___x_8134_, 2, v_bkt_8130_);
                    v_buckets_x27_8135_ =
                        lean_array_uset(v_buckets_8113_, v___x_8129_, v___x_8134_);
                    v___x_8136_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_8137_ = lean_nat_mul(v_size_x27_8133_, v___x_8136_);
                    v___x_8138_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_8139_ = lean_nat_div(v___x_8137_, v___x_8138_);
                    crate::leanh::lean_dec(v___x_8137_);
                    v___x_8140_ = lean_array_get_size(v_buckets_x27_8135_);
                    v___x_8141_ = lean_nat_dec_le(v___x_8139_, v___x_8140_);
                    crate::leanh::lean_dec(v___x_8139_);
                    if v___x_8141_ == 0 {
                        v_val_8142_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(v_buckets_x27_8135_);
                        if v_isShared_8116_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_8115_, 1, v_val_8142_);
                            crate::leanh::lean_ctor_set(v___x_8115_, 0, v_size_x27_8133_);
                            v___x_8144_ = v___x_8115_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_8145_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_8145_,
                                0,
                                v_size_x27_8133_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8145_, 1, v_val_8142_);
                            v___x_8144_ = v_reuseFailAlloc_8145_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_8116_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_8115_, 1, v_buckets_x27_8135_);
                            crate::leanh::lean_ctor_set(v___x_8115_, 0, v_size_x27_8133_);
                            v___x_8147_ = v___x_8115_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_8148_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_8148_,
                                0,
                                v_size_x27_8133_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_8148_,
                                1,
                                v_buckets_x27_8135_,
                            );
                            v___x_8147_ = v_reuseFailAlloc_8148_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_8130_);
                    v___x_8149_ = crate::leanh::lean_box(0);
                    v_buckets_x27_8150_ =
                        lean_array_uset(v_buckets_8113_, v___x_8129_, v___x_8149_);
                    v___x_8151_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_8110_, v_b_8111_, v_bkt_8130_);
                    v___x_8152_ = lean_array_uset(v_buckets_x27_8150_, v___x_8129_, v___x_8151_);
                    if v_isShared_8116_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8115_, 1, v___x_8152_);
                        v___x_8154_ = v___x_8115_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_8155_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8155_, 0, v_size_8112_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8155_, 1, v___x_8152_);
                        v___x_8154_ = v_reuseFailAlloc_8155_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_8144_;
            }
            3 => {
                return v___x_8147_;
            }
            4 => {
                return v___x_8154_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(
    mut v_a_8157_: *mut crate::leanh::LeanObject,
    mut v_x_8158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_8160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_8161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_8162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8163_: u8 = 0;
    let mut v___x_8165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_8158_) == 0 {
                    v___x_8159_ = crate::leanh::lean_box(0);
                    return v___x_8159_;
                } else {
                    v_key_8160_ = crate::leanh::lean_ctor_get(v_x_8158_, 0);
                    v_value_8161_ = crate::leanh::lean_ctor_get(v_x_8158_, 1);
                    v_tail_8162_ = crate::leanh::lean_ctor_get(v_x_8158_, 2);
                    v___x_8163_ = lean_expr_eqv(v_key_8160_, v_a_8157_);
                    if v___x_8163_ == 0 {
                        v_x_8158_ = v_tail_8162_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_8161_);
                        v___x_8165_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_8165_, 0, v_value_8161_);
                        return v___x_8165_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_a_8166_: *mut crate::leanh::LeanObject,
    mut v_x_8167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8168_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_8166_, v_x_8167_);
    crate::leanh::lean_dec(v_x_8167_);
    crate::leanh::lean_dec_ref(v_a_8166_);
    return v_res_8168_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(
    mut v_m_8169_: *mut crate::leanh::LeanObject,
    mut v_a_8170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_8171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8173_: u64 = 0;
    let mut v___x_8174_: u64 = 0;
    let mut v___x_8175_: u64 = 0;
    let mut v_fold_8176_: u64 = 0;
    let mut v___x_8177_: u64 = 0;
    let mut v___x_8178_: u64 = 0;
    let mut v___x_8179_: u64 = 0;
    let mut v___x_8180_: usize = 0;
    let mut v___x_8181_: usize = 0;
    let mut v___x_8182_: usize = 0;
    let mut v___x_8183_: usize = 0;
    let mut v___x_8184_: usize = 0;
    let mut v___x_8185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_8171_ = crate::leanh::lean_ctor_get(v_m_8169_, 1);
    v___x_8172_ = lean_array_get_size(v_buckets_8171_);
    v___x_8173_ = l_Lean_Expr_hash(v_a_8170_);
    v___x_8174_ = 32u64;
    v___x_8175_ = lean_uint64_shift_right(v___x_8173_, v___x_8174_);
    v_fold_8176_ = lean_uint64_xor(v___x_8173_, v___x_8175_);
    v___x_8177_ = 16u64;
    v___x_8178_ = lean_uint64_shift_right(v_fold_8176_, v___x_8177_);
    v___x_8179_ = lean_uint64_xor(v_fold_8176_, v___x_8178_);
    v___x_8180_ = lean_uint64_to_usize(v___x_8179_);
    v___x_8181_ = lean_usize_of_nat(v___x_8172_);
    v___x_8182_ = 1usize;
    v___x_8183_ = lean_usize_sub(v___x_8181_, v___x_8182_);
    v___x_8184_ = lean_usize_land(v___x_8180_, v___x_8183_);
    v___x_8185_ = lean_array_uget_borrowed(v_buckets_8171_, v___x_8184_);
    v___x_8186_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_8170_, v___x_8185_);
    return v___x_8186_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg___boxed(
    mut v_m_8187_: *mut crate::leanh::LeanObject,
    mut v_a_8188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8189_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v_m_8187_, v_a_8188_);
    crate::leanh::lean_dec_ref(v_a_8188_);
    crate::leanh::lean_dec_ref(v_m_8187_);
    return v_res_8189_;
}
pub unsafe fn l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(
    mut v_g_8190_: *mut crate::leanh::LeanObject,
    mut v_e_8191_: *mut crate::leanh::LeanObject,
    mut v_a_8192_: *mut crate::leanh::LeanObject,
    mut v___y_8193_: *mut crate::leanh::LeanObject,
    mut v___y_8194_: *mut crate::leanh::LeanObject,
    mut v___y_8195_: *mut crate::leanh::LeanObject,
    mut v___y_8196_: *mut crate::leanh::LeanObject,
    mut v___y_8197_: *mut crate::leanh::LeanObject,
    mut v___y_8198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_8201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_8214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_8215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8219_: u8 = 0;
    let mut v___x_8220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_8221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_8222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_8223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_8224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_8225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_8226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_8227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_8231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_8232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_8235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_8237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8243_: u8 = 0;
    let mut v___x_8245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8247_: u8 = 0;
    let mut v_val_8248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8251_: u8 = 0;
    let mut v___x_8253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8255_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8209_ = lean_st_ref_get(v_a_8192_);
                v___x_8210_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v___x_8209_, v_e_8191_);
                crate::leanh::lean_dec(v___x_8209_);
                if crate::leanh::lean_obj_tag(v___x_8210_) == 0 {
                    crate::leanh::lean_inc_ref(v_g_8190_);
                    crate::leanh::lean_inc(v___y_8198_);
                    crate::leanh::lean_inc_ref(v___y_8197_);
                    crate::leanh::lean_inc(v___y_8196_);
                    crate::leanh::lean_inc_ref(v___y_8195_);
                    crate::leanh::lean_inc(v___y_8194_);
                    crate::leanh::lean_inc_ref(v___y_8193_);
                    crate::leanh::lean_inc_ref(v_e_8191_);
                    v___x_8211_ = crate::leanh::lean_apply_8(
                        v_g_8190_,
                        v_e_8191_,
                        v___y_8193_,
                        v___y_8194_,
                        v___y_8195_,
                        v___y_8196_,
                        v___y_8197_,
                        v___y_8198_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_8211_) == 0 {
                        v_a_8212_ = crate::leanh::lean_ctor_get(v___x_8211_, 0);
                        crate::leanh::lean_inc(v_a_8212_);
                        crate::leanh::lean_dec_ref_known(v___x_8211_, 1);
                        v___x_8219_ = (crate::leanh::lean_unbox(v_a_8212_) as u8);
                        crate::leanh::lean_dec(v_a_8212_);
                        if v___x_8219_ == 0 {
                            crate::leanh::lean_dec_ref(v_g_8190_);
                            v___x_8220_ = crate::leanh::lean_box(0);
                            v_a_8201_ = v___x_8220_;
                            state = 1;
                            continue;
                        } else {
                            match crate::leanh::lean_obj_tag(v_e_8191_) {
                                7 => {
                                    v_binderType_8221_ = crate::leanh::lean_ctor_get(v_e_8191_, 1);
                                    v_body_8222_ = crate::leanh::lean_ctor_get(v_e_8191_, 2);
                                    crate::leanh::lean_inc_ref(v_body_8222_);
                                    crate::leanh::lean_inc_ref(v_binderType_8221_);
                                    v_d_8214_ = v_binderType_8221_;
                                    v_b_8215_ = v_body_8222_;
                                    v___y_8216_ = v_a_8192_;
                                    state = 3;
                                    continue;
                                }
                                6 => {
                                    v_binderType_8223_ = crate::leanh::lean_ctor_get(v_e_8191_, 1);
                                    v_body_8224_ = crate::leanh::lean_ctor_get(v_e_8191_, 2);
                                    crate::leanh::lean_inc_ref(v_body_8224_);
                                    crate::leanh::lean_inc_ref(v_binderType_8223_);
                                    v_d_8214_ = v_binderType_8223_;
                                    v_b_8215_ = v_body_8224_;
                                    v___y_8216_ = v_a_8192_;
                                    state = 3;
                                    continue;
                                }
                                8 => {
                                    v_type_8225_ = crate::leanh::lean_ctor_get(v_e_8191_, 1);
                                    v_value_8226_ = crate::leanh::lean_ctor_get(v_e_8191_, 2);
                                    v_body_8227_ = crate::leanh::lean_ctor_get(v_e_8191_, 3);
                                    crate::leanh::lean_inc_ref(v_type_8225_);
                                    crate::leanh::lean_inc_ref(v_g_8190_);
                                    v___x_8228_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_8190_, v_type_8225_, v_a_8192_, v___y_8193_, v___y_8194_, v___y_8195_, v___y_8196_, v___y_8197_, v___y_8198_);
                                    if crate::leanh::lean_obj_tag(v___x_8228_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_8228_, 1);
                                        crate::leanh::lean_inc_ref(v_value_8226_);
                                        crate::leanh::lean_inc_ref(v_g_8190_);
                                        v___x_8229_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_8190_, v_value_8226_, v_a_8192_, v___y_8193_, v___y_8194_, v___y_8195_, v___y_8196_, v___y_8197_, v___y_8198_);
                                        if crate::leanh::lean_obj_tag(v___x_8229_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_8229_, 1);
                                            crate::leanh::lean_inc_ref(v_body_8227_);
                                            v___x_8230_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_8190_, v_body_8227_, v_a_8192_, v___y_8193_, v___y_8194_, v___y_8195_, v___y_8196_, v___y_8197_, v___y_8198_);
                                            v___y_8207_ = v___x_8230_;
                                            state = 2;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec_ref(v_g_8190_);
                                            v___y_8207_ = v___x_8229_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_g_8190_);
                                        v___y_8207_ = v___x_8228_;
                                        state = 2;
                                        continue;
                                    }
                                }
                                5 => {
                                    v_fn_8231_ = crate::leanh::lean_ctor_get(v_e_8191_, 0);
                                    v_arg_8232_ = crate::leanh::lean_ctor_get(v_e_8191_, 1);
                                    crate::leanh::lean_inc_ref(v_fn_8231_);
                                    crate::leanh::lean_inc_ref(v_g_8190_);
                                    v___x_8233_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_8190_, v_fn_8231_, v_a_8192_, v___y_8193_, v___y_8194_, v___y_8195_, v___y_8196_, v___y_8197_, v___y_8198_);
                                    if crate::leanh::lean_obj_tag(v___x_8233_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_8233_, 1);
                                        crate::leanh::lean_inc_ref(v_arg_8232_);
                                        v___x_8234_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_8190_, v_arg_8232_, v_a_8192_, v___y_8193_, v___y_8194_, v___y_8195_, v___y_8196_, v___y_8197_, v___y_8198_);
                                        v___y_8207_ = v___x_8234_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec_ref(v_g_8190_);
                                        v___y_8207_ = v___x_8233_;
                                        state = 2;
                                        continue;
                                    }
                                }
                                10 => {
                                    v_expr_8235_ = crate::leanh::lean_ctor_get(v_e_8191_, 1);
                                    crate::leanh::lean_inc_ref(v_expr_8235_);
                                    v___x_8236_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_8190_, v_expr_8235_, v_a_8192_, v___y_8193_, v___y_8194_, v___y_8195_, v___y_8196_, v___y_8197_, v___y_8198_);
                                    v___y_8207_ = v___x_8236_;
                                    state = 2;
                                    continue;
                                }
                                11 => {
                                    v_struct_8237_ = crate::leanh::lean_ctor_get(v_e_8191_, 2);
                                    crate::leanh::lean_inc_ref(v_struct_8237_);
                                    v___x_8238_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_8190_, v_struct_8237_, v_a_8192_, v___y_8193_, v___y_8194_, v___y_8195_, v___y_8196_, v___y_8197_, v___y_8198_);
                                    v___y_8207_ = v___x_8238_;
                                    state = 2;
                                    continue;
                                }
                                _ => {
                                    crate::leanh::lean_dec_ref(v_g_8190_);
                                    v___x_8239_ = crate::leanh::lean_box(0);
                                    v_a_8201_ = v___x_8239_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_8191_);
                        crate::leanh::lean_dec_ref(v_g_8190_);
                        v_a_8240_ = crate::leanh::lean_ctor_get(v___x_8211_, 0);
                        v_isSharedCheck_8247_ =
                            (!crate::leanh::lean_is_exclusive(v___x_8211_)) as u8;
                        if v_isSharedCheck_8247_ == 0 {
                            v___x_8242_ = v___x_8211_;
                            v_isShared_8243_ = v_isSharedCheck_8247_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_8240_);
                            crate::leanh::lean_dec(v___x_8211_);
                            v___x_8242_ = crate::leanh::lean_box(0);
                            v_isShared_8243_ = v_isSharedCheck_8247_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_8191_);
                    crate::leanh::lean_dec_ref(v_g_8190_);
                    v_val_8248_ = crate::leanh::lean_ctor_get(v___x_8210_, 0);
                    v_isSharedCheck_8255_ = (!crate::leanh::lean_is_exclusive(v___x_8210_)) as u8;
                    if v_isSharedCheck_8255_ == 0 {
                        v___x_8250_ = v___x_8210_;
                        v_isShared_8251_ = v_isSharedCheck_8255_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_8248_);
                        crate::leanh::lean_dec(v___x_8210_);
                        v___x_8250_ = crate::leanh::lean_box(0);
                        v_isShared_8251_ = v_isSharedCheck_8255_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8202_ = lean_st_ref_take(v_a_8192_);
                v___x_8203_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(v___x_8202_, v_e_8191_, v_a_8201_);
                v___x_8204_ = lean_st_ref_set(v_a_8192_, v___x_8203_);
                v___x_8205_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_8205_, 0, v_a_8201_);
                return v___x_8205_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_8207_) == 0 {
                    v_a_8208_ = crate::leanh::lean_ctor_get(v___y_8207_, 0);
                    crate::leanh::lean_inc(v_a_8208_);
                    crate::leanh::lean_dec_ref_known(v___y_8207_, 1);
                    v_a_8201_ = v_a_8208_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_e_8191_);
                    return v___y_8207_;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v_g_8190_);
                v___x_8217_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(
                    v_g_8190_,
                    v_d_8214_,
                    v___y_8216_,
                    v___y_8193_,
                    v___y_8194_,
                    v___y_8195_,
                    v___y_8196_,
                    v___y_8197_,
                    v___y_8198_,
                );
                if crate::leanh::lean_obj_tag(v___x_8217_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_8217_, 1);
                    v___x_8218_ =
                        l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(
                            v_g_8190_,
                            v_b_8215_,
                            v___y_8216_,
                            v___y_8193_,
                            v___y_8194_,
                            v___y_8195_,
                            v___y_8196_,
                            v___y_8197_,
                            v___y_8198_,
                        );
                    v___y_8207_ = v___x_8218_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_b_8215_);
                    crate::leanh::lean_dec_ref(v_g_8190_);
                    v___y_8207_ = v___x_8217_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                if v_isShared_8243_ == 0 {
                    v___x_8245_ = v___x_8242_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8246_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8246_, 0, v_a_8240_);
                    v___x_8245_ = v_reuseFailAlloc_8246_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_8245_;
            }
            6 => {
                if v_isShared_8251_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_8250_, 0);
                    v___x_8253_ = v___x_8250_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8254_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8254_, 0, v_val_8248_);
                    v___x_8253_ = v_reuseFailAlloc_8254_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_8253_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1___boxed(
    mut v_g_8256_: *mut crate::leanh::LeanObject,
    mut v_e_8257_: *mut crate::leanh::LeanObject,
    mut v_a_8258_: *mut crate::leanh::LeanObject,
    mut v___y_8259_: *mut crate::leanh::LeanObject,
    mut v___y_8260_: *mut crate::leanh::LeanObject,
    mut v___y_8261_: *mut crate::leanh::LeanObject,
    mut v___y_8262_: *mut crate::leanh::LeanObject,
    mut v___y_8263_: *mut crate::leanh::LeanObject,
    mut v___y_8264_: *mut crate::leanh::LeanObject,
    mut v___y_8265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8266_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(
        v_g_8256_,
        v_e_8257_,
        v_a_8258_,
        v___y_8259_,
        v___y_8260_,
        v___y_8261_,
        v___y_8262_,
        v___y_8263_,
        v___y_8264_,
    );
    crate::leanh::lean_dec(v___y_8264_);
    crate::leanh::lean_dec_ref(v___y_8263_);
    crate::leanh::lean_dec(v___y_8262_);
    crate::leanh::lean_dec_ref(v___y_8261_);
    crate::leanh::lean_dec(v___y_8260_);
    crate::leanh::lean_dec_ref(v___y_8259_);
    crate::leanh::lean_dec(v_a_8258_);
    return v_res_8266_;
}
pub unsafe fn l_Lean_Expr_checkMaxShared(
    mut v_e_8267_: *mut crate::leanh::LeanObject,
    mut v_msg_8268_: *mut crate::leanh::LeanObject,
    mut v_a_8269_: *mut crate::leanh::LeanObject,
    mut v_a_8270_: *mut crate::leanh::LeanObject,
    mut v_a_8271_: *mut crate::leanh::LeanObject,
    mut v_a_8272_: *mut crate::leanh::LeanObject,
    mut v_a_8273_: *mut crate::leanh::LeanObject,
    mut v_a_8274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8283_: u8 = 0;
    let mut v___x_8284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8288_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8276_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once), _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
                v___x_8277_ = lean_st_mk_ref(v___x_8276_);
                v___f_8278_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Expr_checkMaxShared___lam__0___boxed as *mut core::ffi::c_void,
                    9,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_8278_, 0, v_msg_8268_);
                v___x_8279_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(
                    v___f_8278_,
                    v_e_8267_,
                    v___x_8277_,
                    v_a_8269_,
                    v_a_8270_,
                    v_a_8271_,
                    v_a_8272_,
                    v_a_8273_,
                    v_a_8274_,
                );
                if crate::leanh::lean_obj_tag(v___x_8279_) == 0 {
                    v_a_8280_ = crate::leanh::lean_ctor_get(v___x_8279_, 0);
                    v_isSharedCheck_8288_ = (!crate::leanh::lean_is_exclusive(v___x_8279_)) as u8;
                    if v_isSharedCheck_8288_ == 0 {
                        v___x_8282_ = v___x_8279_;
                        v_isShared_8283_ = v_isSharedCheck_8288_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8280_);
                        crate::leanh::lean_dec(v___x_8279_);
                        v___x_8282_ = crate::leanh::lean_box(0);
                        v_isShared_8283_ = v_isSharedCheck_8288_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_8277_);
                    return v___x_8279_;
                }
            }
            1 => {
                v___x_8284_ = lean_st_ref_get(v___x_8277_);
                crate::leanh::lean_dec(v___x_8277_);
                crate::leanh::lean_dec(v___x_8284_);
                if v_isShared_8283_ == 0 {
                    v___x_8286_ = v___x_8282_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8287_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8287_, 0, v_a_8280_);
                    v___x_8286_ = v_reuseFailAlloc_8287_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8286_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_checkMaxShared___boxed(
    mut v_e_8289_: *mut crate::leanh::LeanObject,
    mut v_msg_8290_: *mut crate::leanh::LeanObject,
    mut v_a_8291_: *mut crate::leanh::LeanObject,
    mut v_a_8292_: *mut crate::leanh::LeanObject,
    mut v_a_8293_: *mut crate::leanh::LeanObject,
    mut v_a_8294_: *mut crate::leanh::LeanObject,
    mut v_a_8295_: *mut crate::leanh::LeanObject,
    mut v_a_8296_: *mut crate::leanh::LeanObject,
    mut v_a_8297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8298_ = l_Lean_Expr_checkMaxShared(
        v_e_8289_,
        v_msg_8290_,
        v_a_8291_,
        v_a_8292_,
        v_a_8293_,
        v_a_8294_,
        v_a_8295_,
        v_a_8296_,
    );
    crate::leanh::lean_dec(v_a_8296_);
    crate::leanh::lean_dec_ref(v_a_8295_);
    crate::leanh::lean_dec(v_a_8294_);
    crate::leanh::lean_dec_ref(v_a_8293_);
    crate::leanh::lean_dec(v_a_8292_);
    crate::leanh::lean_dec_ref(v_a_8291_);
    return v_res_8298_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0(
    mut v_00_u03b2_8299_: *mut crate::leanh::LeanObject,
    mut v_x_8300_: *mut crate::leanh::LeanObject,
    mut v_x_8301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8302_ =
        l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(
            v_x_8300_, v_x_8301_,
        );
    return v___x_8302_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___boxed(
    mut v_00_u03b2_8303_: *mut crate::leanh::LeanObject,
    mut v_x_8304_: *mut crate::leanh::LeanObject,
    mut v_x_8305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8306_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0(
        v_00_u03b2_8303_,
        v_x_8304_,
        v_x_8305_,
    );
    crate::leanh::lean_dec_ref(v_x_8304_);
    return v_res_8306_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0(
    mut v_00_u03b2_8307_: *mut crate::leanh::LeanObject,
    mut v_x_8308_: *mut crate::leanh::LeanObject,
    mut v_x_8309_: usize,
    mut v_x_8310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_x_8308_);
    v___x_8311_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_8308_, v_x_8309_, v_x_8310_);
    return v___x_8311_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___boxed(
    mut v_00_u03b2_8312_: *mut crate::leanh::LeanObject,
    mut v_x_8313_: *mut crate::leanh::LeanObject,
    mut v_x_8314_: *mut crate::leanh::LeanObject,
    mut v_x_8315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_8019__boxed_8316_: usize = 0;
    let mut v_res_8317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_8019__boxed_8316_ = crate::leanh::lean_unbox_usize(v_x_8314_);
    crate::leanh::lean_dec(v_x_8314_);
    v_res_8317_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0(v_00_u03b2_8312_, v_x_8313_, v_x_8019__boxed_8316_, v_x_8315_);
    crate::leanh::lean_dec_ref(v_x_8313_);
    return v_res_8317_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2(
    mut v_00_u03b2_8318_: *mut crate::leanh::LeanObject,
    mut v_m_8319_: *mut crate::leanh::LeanObject,
    mut v_a_8320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8321_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v_m_8319_, v_a_8320_);
    return v___x_8321_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___boxed(
    mut v_00_u03b2_8322_: *mut crate::leanh::LeanObject,
    mut v_m_8323_: *mut crate::leanh::LeanObject,
    mut v_a_8324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8325_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2(v_00_u03b2_8322_, v_m_8323_, v_a_8324_);
    crate::leanh::lean_dec_ref(v_a_8324_);
    crate::leanh::lean_dec_ref(v_m_8323_);
    return v_res_8325_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3(
    mut v_00_u03b2_8326_: *mut crate::leanh::LeanObject,
    mut v_m_8327_: *mut crate::leanh::LeanObject,
    mut v_a_8328_: *mut crate::leanh::LeanObject,
    mut v_b_8329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8330_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(v_m_8327_, v_a_8328_, v_b_8329_);
    return v___x_8330_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1(
    mut v_00_u03b2_8331_: *mut crate::leanh::LeanObject,
    mut v_keys_8332_: *mut crate::leanh::LeanObject,
    mut v_vals_8333_: *mut crate::leanh::LeanObject,
    mut v_heq_8334_: *mut crate::leanh::LeanObject,
    mut v_i_8335_: *mut crate::leanh::LeanObject,
    mut v_k_8336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8337_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_keys_8332_, v_vals_8333_, v_i_8335_, v_k_8336_);
    return v___x_8337_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_8338_: *mut crate::leanh::LeanObject,
    mut v_keys_8339_: *mut crate::leanh::LeanObject,
    mut v_vals_8340_: *mut crate::leanh::LeanObject,
    mut v_heq_8341_: *mut crate::leanh::LeanObject,
    mut v_i_8342_: *mut crate::leanh::LeanObject,
    mut v_k_8343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8344_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1(v_00_u03b2_8338_, v_keys_8339_, v_vals_8340_, v_heq_8341_, v_i_8342_, v_k_8343_);
    crate::leanh::lean_dec_ref(v_vals_8340_);
    crate::leanh::lean_dec_ref(v_keys_8339_);
    return v_res_8344_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4(
    mut v_00_u03b2_8345_: *mut crate::leanh::LeanObject,
    mut v_a_8346_: *mut crate::leanh::LeanObject,
    mut v_x_8347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8348_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_8346_, v_x_8347_);
    return v___x_8348_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b2_8349_: *mut crate::leanh::LeanObject,
    mut v_a_8350_: *mut crate::leanh::LeanObject,
    mut v_x_8351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8352_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4(v_00_u03b2_8349_, v_a_8350_, v_x_8351_);
    crate::leanh::lean_dec(v_x_8351_);
    crate::leanh::lean_dec_ref(v_a_8350_);
    return v_res_8352_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6(
    mut v_00_u03b2_8353_: *mut crate::leanh::LeanObject,
    mut v_a_8354_: *mut crate::leanh::LeanObject,
    mut v_x_8355_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_8356_: u8 = 0;
    v___x_8356_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_8354_, v_x_8355_);
    return v___x_8356_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___boxed(
    mut v_00_u03b2_8357_: *mut crate::leanh::LeanObject,
    mut v_a_8358_: *mut crate::leanh::LeanObject,
    mut v_x_8359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8360_: u8 = 0;
    let mut v_r_8361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8360_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6(v_00_u03b2_8357_, v_a_8358_, v_x_8359_);
    crate::leanh::lean_dec(v_x_8359_);
    crate::leanh::lean_dec_ref(v_a_8358_);
    v_r_8361_ = crate::leanh::lean_box((v_res_8360_) as usize);
    return v_r_8361_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7(
    mut v_00_u03b2_8362_: *mut crate::leanh::LeanObject,
    mut v_data_8363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8364_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(v_data_8363_);
    return v___x_8364_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8(
    mut v_00_u03b2_8365_: *mut crate::leanh::LeanObject,
    mut v_a_8366_: *mut crate::leanh::LeanObject,
    mut v_b_8367_: *mut crate::leanh::LeanObject,
    mut v_x_8368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8369_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_8366_, v_b_8367_, v_x_8368_);
    return v___x_8369_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8(
    mut v_00_u03b2_8370_: *mut crate::leanh::LeanObject,
    mut v_i_8371_: *mut crate::leanh::LeanObject,
    mut v_source_8372_: *mut crate::leanh::LeanObject,
    mut v_target_8373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8374_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(v_i_8371_, v_source_8372_, v_target_8373_);
    return v___x_8374_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9(
    mut v_00_u03b2_8375_: *mut crate::leanh::LeanObject,
    mut v_x_8376_: *mut crate::leanh::LeanObject,
    mut v_x_8377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8378_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(v_x_8376_, v_x_8377_);
    return v___x_8378_;
}
pub unsafe fn l_Lean_MVarId_checkMaxShared(
    mut v_mvarId_8379_: *mut crate::leanh::LeanObject,
    mut v_msg_8380_: *mut crate::leanh::LeanObject,
    mut v_a_8381_: *mut crate::leanh::LeanObject,
    mut v_a_8382_: *mut crate::leanh::LeanObject,
    mut v_a_8383_: *mut crate::leanh::LeanObject,
    mut v_a_8384_: *mut crate::leanh::LeanObject,
    mut v_a_8385_: *mut crate::leanh::LeanObject,
    mut v_a_8386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_8390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8395_: u8 = 0;
    let mut v___x_8397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8399_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8388_ = l_Lean_MVarId_getDecl(
                    v_mvarId_8379_,
                    v_a_8383_,
                    v_a_8384_,
                    v_a_8385_,
                    v_a_8386_,
                );
                if crate::leanh::lean_obj_tag(v___x_8388_) == 0 {
                    v_a_8389_ = crate::leanh::lean_ctor_get(v___x_8388_, 0);
                    crate::leanh::lean_inc(v_a_8389_);
                    crate::leanh::lean_dec_ref_known(v___x_8388_, 1);
                    v_type_8390_ = crate::leanh::lean_ctor_get(v_a_8389_, 2);
                    crate::leanh::lean_inc_ref(v_type_8390_);
                    crate::leanh::lean_dec(v_a_8389_);
                    v___x_8391_ = l_Lean_Expr_checkMaxShared(
                        v_type_8390_,
                        v_msg_8380_,
                        v_a_8381_,
                        v_a_8382_,
                        v_a_8383_,
                        v_a_8384_,
                        v_a_8385_,
                        v_a_8386_,
                    );
                    return v___x_8391_;
                } else {
                    crate::leanh::lean_dec_ref(v_msg_8380_);
                    v_a_8392_ = crate::leanh::lean_ctor_get(v___x_8388_, 0);
                    v_isSharedCheck_8399_ = (!crate::leanh::lean_is_exclusive(v___x_8388_)) as u8;
                    if v_isSharedCheck_8399_ == 0 {
                        v___x_8394_ = v___x_8388_;
                        v_isShared_8395_ = v_isSharedCheck_8399_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8392_);
                        crate::leanh::lean_dec(v___x_8388_);
                        v___x_8394_ = crate::leanh::lean_box(0);
                        v_isShared_8395_ = v_isSharedCheck_8399_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8395_ == 0 {
                    v___x_8397_ = v___x_8394_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8398_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8398_, 0, v_a_8392_);
                    v___x_8397_ = v_reuseFailAlloc_8398_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8397_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_checkMaxShared___boxed(
    mut v_mvarId_8400_: *mut crate::leanh::LeanObject,
    mut v_msg_8401_: *mut crate::leanh::LeanObject,
    mut v_a_8402_: *mut crate::leanh::LeanObject,
    mut v_a_8403_: *mut crate::leanh::LeanObject,
    mut v_a_8404_: *mut crate::leanh::LeanObject,
    mut v_a_8405_: *mut crate::leanh::LeanObject,
    mut v_a_8406_: *mut crate::leanh::LeanObject,
    mut v_a_8407_: *mut crate::leanh::LeanObject,
    mut v_a_8408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8409_ = l_Lean_MVarId_checkMaxShared(
        v_mvarId_8400_,
        v_msg_8401_,
        v_a_8402_,
        v_a_8403_,
        v_a_8404_,
        v_a_8405_,
        v_a_8406_,
        v_a_8407_,
    );
    crate::leanh::lean_dec(v_a_8407_);
    crate::leanh::lean_dec_ref(v_a_8406_);
    crate::leanh::lean_dec(v_a_8405_);
    crate::leanh::lean_dec_ref(v_a_8404_);
    crate::leanh::lean_dec(v_a_8403_);
    crate::leanh::lean_dec_ref(v_a_8402_);
    return v_res_8409_;
}
pub unsafe fn l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(
    mut v_x_8410_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_8411_: u8 = 0;
    let mut v_head_8412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_8413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8414_: u8 = 0;
    let mut v___x_8415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_8410_) == 0 {
                    v___x_8411_ = 0;
                    return v___x_8411_;
                } else {
                    v_head_8412_ = crate::leanh::lean_ctor_get(v_x_8410_, 0);
                    v_tail_8413_ = crate::leanh::lean_ctor_get(v_x_8410_, 1);
                    v___x_8414_ = l_Lean_Level_isAlreadyNormalizedCheap(v_head_8412_);
                    if v___x_8414_ == 0 {
                        v___x_8415_ = 1;
                        return v___x_8415_;
                    } else {
                        v_x_8410_ = v_tail_8413_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0___boxed(
    mut v_x_8417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8418_: u8 = 0;
    let mut v_r_8419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8418_ = l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(v_x_8417_);
    crate::leanh::lean_dec(v_x_8417_);
    v_r_8419_ = crate::leanh::lean_box((v_res_8418_) as usize);
    return v_r_8419_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0(
    mut v_x_8420_: *mut crate::leanh::LeanObject,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_x_8420_) {
        4 => {
            let mut v_us_8421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8422_: u8 = 0;
            v_us_8421_ = crate::leanh::lean_ctor_get(v_x_8420_, 1);
            v___x_8422_ = l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(v_us_8421_);
            return v___x_8422_;
        }
        3 => {
            let mut v_u_8423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8424_: u8 = 0;
            v_u_8423_ = crate::leanh::lean_ctor_get(v_x_8420_, 0);
            v___x_8424_ = l_Lean_Level_isAlreadyNormalizedCheap(v_u_8423_);
            if v___x_8424_ == 0 {
                let mut v___x_8425_: u8 = 0;
                v___x_8425_ = 1;
                return v___x_8425_;
            } else {
                let mut v___x_8426_: u8 = 0;
                v___x_8426_ = 0;
                return v___x_8426_;
            }
        }
        _ => {
            let mut v___x_8427_: u8 = 0;
            v___x_8427_ = 0;
            return v___x_8427_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0___boxed(
    mut v_x_8428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8429_: u8 = 0;
    let mut v_r_8430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8429_ =
        l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0(v_x_8428_);
    crate::leanh::lean_dec_ref(v_x_8428_);
    v_r_8430_ = crate::leanh::lean_box((v_res_8429_) as usize);
    return v_r_8430_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(
    mut v_e_8432_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_8433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_8433_ =
        l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___closed__0;
    v___x_8434_ = lean_find_expr(v___f_8433_, v_e_8432_);
    if crate::leanh::lean_obj_tag(v___x_8434_) == 0 {
        let mut v___x_8435_: u8 = 0;
        v___x_8435_ = 1;
        return v___x_8435_;
    } else {
        let mut v___x_8436_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_8434_, 1);
        v___x_8436_ = 0;
        return v___x_8436_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___boxed(
    mut v_e_8437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8438_: u8 = 0;
    let mut v_r_8439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8438_ =
        l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(v_e_8437_);
    crate::leanh::lean_dec_ref(v_e_8437_);
    v_r_8439_ = crate::leanh::lean_box((v_res_8438_) as usize);
    return v_r_8439_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Sym_normalizeLevels_spec__0(
    mut v_a_8440_: *mut crate::leanh::LeanObject,
    mut v_a_8441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_8443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_8444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8447_: u8 = 0;
    let mut v___x_8448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8453_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_8440_) == 0 {
                    v___x_8442_ = l_List_reverse___redArg(v_a_8441_);
                    return v___x_8442_;
                } else {
                    v_head_8443_ = crate::leanh::lean_ctor_get(v_a_8440_, 0);
                    v_tail_8444_ = crate::leanh::lean_ctor_get(v_a_8440_, 1);
                    v_isSharedCheck_8453_ = (!crate::leanh::lean_is_exclusive(v_a_8440_)) as u8;
                    if v_isSharedCheck_8453_ == 0 {
                        v___x_8446_ = v_a_8440_;
                        v_isShared_8447_ = v_isSharedCheck_8453_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_8444_);
                        crate::leanh::lean_inc(v_head_8443_);
                        crate::leanh::lean_dec(v_a_8440_);
                        v___x_8446_ = crate::leanh::lean_box(0);
                        v_isShared_8447_ = v_isSharedCheck_8453_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8448_ = l_Lean_Level_normalize(v_head_8443_);
                crate::leanh::lean_dec(v_head_8443_);
                if v_isShared_8447_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8446_, 1, v_a_8441_);
                    crate::leanh::lean_ctor_set(v___x_8446_, 0, v___x_8448_);
                    v___x_8450_ = v___x_8446_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8452_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8452_, 0, v___x_8448_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8452_, 1, v_a_8441_);
                    v___x_8450_ = v_reuseFailAlloc_8452_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_8440_ = v_tail_8444_;
                v_a_8441_ = v___x_8450_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_normalizeLevels___lam__0(
    mut v_e_8454_: *mut crate::leanh::LeanObject,
    mut v___y_8455_: *mut crate::leanh::LeanObject,
    mut v___y_8456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_8459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_8466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8468_: usize = 0;
    let mut v___x_8469_: usize = 0;
    let mut v___x_8470_: u8 = 0;
    let mut v___x_8471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_8472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_8473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8476_: u8 = 0;
    let mut v___x_8477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_8454_) {
                3 => {
                    v_u_8466_ = crate::leanh::lean_ctor_get(v_e_8454_, 0);
                    v___x_8467_ = l_Lean_Level_normalize(v_u_8466_);
                    v___x_8468_ = lean_ptr_addr(v_u_8466_);
                    v___x_8469_ = lean_ptr_addr(v___x_8467_);
                    v___x_8470_ = lean_usize_dec_eq(v___x_8468_, v___x_8469_);
                    if v___x_8470_ == 0 {
                        crate::leanh::lean_dec_ref_known(v_e_8454_, 1);
                        v___x_8471_ = l_Lean_Expr_sort___override(v___x_8467_);
                        v___y_8459_ = v___x_8471_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_8467_);
                        v___y_8459_ = v_e_8454_;
                        state = 1;
                        continue;
                    }
                }
                4 => {
                    v_declName_8472_ = crate::leanh::lean_ctor_get(v_e_8454_, 0);
                    v_us_8473_ = crate::leanh::lean_ctor_get(v_e_8454_, 1);
                    v___x_8474_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_us_8473_);
                    v___x_8475_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_normalizeLevels_spec__0(
                        v_us_8473_,
                        v___x_8474_,
                    );
                    v___x_8476_ = l_ptrEqList___redArg(v_us_8473_, v___x_8475_);
                    if v___x_8476_ == 0 {
                        crate::leanh::lean_inc(v_declName_8472_);
                        crate::leanh::lean_dec_ref_known(v_e_8454_, 2);
                        v___x_8477_ = l_Lean_Expr_const___override(v_declName_8472_, v___x_8475_);
                        v___y_8463_ = v___x_8477_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_8475_);
                        v___y_8463_ = v_e_8454_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_e_8454_);
                    v___x_8478_ = l_Lean_Meta_Sym_unfoldReducibleStep___closed__0;
                    v___x_8479_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_8479_, 0, v___x_8478_);
                    return v___x_8479_;
                }
            },
            1 => {
                v___x_8460_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_8460_, 0, v___y_8459_);
                v___x_8461_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_8461_, 0, v___x_8460_);
                return v___x_8461_;
            }
            2 => {
                v___x_8464_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_8464_, 0, v___y_8463_);
                v___x_8465_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_8465_, 0, v___x_8464_);
                return v___x_8465_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_normalizeLevels___lam__0___boxed(
    mut v_e_8480_: *mut crate::leanh::LeanObject,
    mut v___y_8481_: *mut crate::leanh::LeanObject,
    mut v___y_8482_: *mut crate::leanh::LeanObject,
    mut v___y_8483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8484_ = l_Lean_Meta_Sym_normalizeLevels___lam__0(v_e_8480_, v___y_8481_, v___y_8482_);
    crate::leanh::lean_dec(v___y_8482_);
    crate::leanh::lean_dec_ref(v___y_8481_);
    return v_res_8484_;
}
pub unsafe fn l_Lean_Meta_Sym_normalizeLevels___lam__1(
    mut v_e_8485_: *mut crate::leanh::LeanObject,
    mut v___y_8486_: *mut crate::leanh::LeanObject,
    mut v___y_8487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8489_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_8489_, 0, v_e_8485_);
    v___x_8490_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_8490_, 0, v___x_8489_);
    return v___x_8490_;
}
pub unsafe fn l_Lean_Meta_Sym_normalizeLevels___lam__1___boxed(
    mut v_e_8491_: *mut crate::leanh::LeanObject,
    mut v___y_8492_: *mut crate::leanh::LeanObject,
    mut v___y_8493_: *mut crate::leanh::LeanObject,
    mut v___y_8494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8495_ = l_Lean_Meta_Sym_normalizeLevels___lam__1(v_e_8491_, v___y_8492_, v___y_8493_);
    crate::leanh::lean_dec(v___y_8493_);
    crate::leanh::lean_dec_ref(v___y_8492_);
    return v_res_8495_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg(
    mut v_ref_8496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8498_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
    v___x_8499_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_8499_, 0, v_ref_8496_);
    crate::leanh::lean_ctor_set(v___x_8499_, 1, v___x_8498_);
    v___x_8500_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_8500_, 0, v___x_8499_);
    return v___x_8500_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg___boxed(
    mut v_ref_8501_: *mut crate::leanh::LeanObject,
    mut v___y_8502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8503_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg(v_ref_8501_);
    return v_res_8503_;
}
pub unsafe fn _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_8504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8504_ = crate::leanh::lean_box(0);
    v___x_8505_ = l_Lean_interruptExceptionId;
    v___x_8506_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_8506_, 0, v___x_8505_);
    crate::leanh::lean_ctor_set(v___x_8506_, 1, v___x_8504_);
    return v___x_8506_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_8508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8508_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___closed__0_once), _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___closed__0);
    v___x_8509_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_8509_, 0, v___x_8508_);
    return v___x_8509_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___boxed(
    mut v___y_8510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8511_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg();
    return v_res_8511_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg(
    mut v_x_8512_: *mut crate::leanh::LeanObject,
    mut v___y_8513_: *mut crate::leanh::LeanObject,
    mut v___y_8514_: *mut crate::leanh::LeanObject,
    mut v___y_8515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_8518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8522_: u8 = 0;
    let mut v___x_8524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8526_: u8 = 0;
    let mut v___y_8528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8530_: u8 = 0;
    let mut v___y_8531_: u8 = 0;
    let mut v___y_8532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_8548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_8549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_8550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_8551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_8552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_8553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_8554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_8555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_8556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_8557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_8558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_8559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_8560_: u8 = 0;
    let mut v_cancelTk_x3f_8561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_8562_: u8 = 0;
    let mut v_inheritedTraceOptions_8563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8566_: u8 = 0;
    let mut v___x_8567_: u8 = 0;
    let mut v___x_8568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8570_: u8 = 0;
    let mut v___x_8571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8575_: u8 = 0;
    let mut v___x_8577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8579_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_8548_ = crate::leanh::lean_ctor_get(v___y_8514_, 0);
                v_fileMap_8549_ = crate::leanh::lean_ctor_get(v___y_8514_, 1);
                v_options_8550_ = crate::leanh::lean_ctor_get(v___y_8514_, 2);
                v_currRecDepth_8551_ = crate::leanh::lean_ctor_get(v___y_8514_, 3);
                v_maxRecDepth_8552_ = crate::leanh::lean_ctor_get(v___y_8514_, 4);
                v_ref_8553_ = crate::leanh::lean_ctor_get(v___y_8514_, 5);
                v_currNamespace_8554_ = crate::leanh::lean_ctor_get(v___y_8514_, 6);
                v_openDecls_8555_ = crate::leanh::lean_ctor_get(v___y_8514_, 7);
                v_initHeartbeats_8556_ = crate::leanh::lean_ctor_get(v___y_8514_, 8);
                v_maxHeartbeats_8557_ = crate::leanh::lean_ctor_get(v___y_8514_, 9);
                v_quotContext_8558_ = crate::leanh::lean_ctor_get(v___y_8514_, 10);
                v_currMacroScope_8559_ = crate::leanh::lean_ctor_get(v___y_8514_, 11);
                v_diag_8560_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_8514_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_8561_ = crate::leanh::lean_ctor_get(v___y_8514_, 12);
                v_suppressElabErrors_8562_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_8514_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_8563_ = crate::leanh::lean_ctor_get(v___y_8514_, 13);
                if crate::leanh::lean_obj_tag(v_cancelTk_x3f_8561_) == 1 {
                    v_val_8569_ = crate::leanh::lean_ctor_get(v_cancelTk_x3f_8561_, 0);
                    v___x_8570_ = l_IO_CancelToken_isSet(v_val_8569_);
                    if v___x_8570_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_x_8512_);
                        v___x_8571_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg();
                        v_a_8572_ = crate::leanh::lean_ctor_get(v___x_8571_, 0);
                        v_isSharedCheck_8579_ =
                            (!crate::leanh::lean_is_exclusive(v___x_8571_)) as u8;
                        if v_isSharedCheck_8579_ == 0 {
                            v___x_8574_ = v___x_8571_;
                            v_isShared_8575_ = v_isSharedCheck_8579_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_8572_);
                            crate::leanh::lean_dec(v___x_8571_);
                            v___x_8574_ = crate::leanh::lean_box(0);
                            v_isShared_8575_ = v_isSharedCheck_8579_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    state = 5;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_8518_) == 0 {
                    return v___y_8518_;
                } else {
                    v_a_8519_ = crate::leanh::lean_ctor_get(v___y_8518_, 0);
                    v_isSharedCheck_8526_ = (!crate::leanh::lean_is_exclusive(v___y_8518_)) as u8;
                    if v_isSharedCheck_8526_ == 0 {
                        v___x_8521_ = v___y_8518_;
                        v_isShared_8522_ = v_isSharedCheck_8526_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8519_);
                        crate::leanh::lean_dec(v___y_8518_);
                        v___x_8521_ = crate::leanh::lean_box(0);
                        v_isShared_8522_ = v_isSharedCheck_8526_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_8522_ == 0 {
                    v___x_8524_ = v___x_8521_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8525_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8525_, 0, v_a_8519_);
                    v___x_8524_ = v_reuseFailAlloc_8525_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_8524_;
            }
            4 => {
                v___x_8544_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_8545_ = lean_nat_add(v___y_8536_, v___x_8544_);
                crate::leanh::lean_inc_ref(v___y_8532_);
                crate::leanh::lean_inc(v___y_8528_);
                crate::leanh::lean_inc(v___y_8540_);
                crate::leanh::lean_inc(v___y_8533_);
                crate::leanh::lean_inc(v___y_8543_);
                crate::leanh::lean_inc(v___y_8534_);
                crate::leanh::lean_inc(v___y_8535_);
                crate::leanh::lean_inc(v___y_8539_);
                crate::leanh::lean_inc(v___y_8538_);
                crate::leanh::lean_inc_ref(v___y_8542_);
                crate::leanh::lean_inc_ref(v___y_8541_);
                crate::leanh::lean_inc_ref(v___y_8537_);
                v___x_8546_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_8546_, 0, v___y_8537_);
                crate::leanh::lean_ctor_set(v___x_8546_, 1, v___y_8541_);
                crate::leanh::lean_ctor_set(v___x_8546_, 2, v___y_8542_);
                crate::leanh::lean_ctor_set(v___x_8546_, 3, v___x_8545_);
                crate::leanh::lean_ctor_set(v___x_8546_, 4, v___y_8538_);
                crate::leanh::lean_ctor_set(v___x_8546_, 5, v___y_8529_);
                crate::leanh::lean_ctor_set(v___x_8546_, 6, v___y_8539_);
                crate::leanh::lean_ctor_set(v___x_8546_, 7, v___y_8535_);
                crate::leanh::lean_ctor_set(v___x_8546_, 8, v___y_8534_);
                crate::leanh::lean_ctor_set(v___x_8546_, 9, v___y_8543_);
                crate::leanh::lean_ctor_set(v___x_8546_, 10, v___y_8533_);
                crate::leanh::lean_ctor_set(v___x_8546_, 11, v___y_8540_);
                crate::leanh::lean_ctor_set(v___x_8546_, 12, v___y_8528_);
                crate::leanh::lean_ctor_set(v___x_8546_, 13, v___y_8532_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_8546_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v___y_8530_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_8546_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v___y_8531_,
                );
                crate::leanh::lean_inc(v___y_8515_);
                crate::leanh::lean_inc(v___y_8513_);
                v___x_8547_ = crate::leanh::lean_apply_4(
                    v_x_8512_,
                    v___y_8513_,
                    v___x_8546_,
                    v___y_8515_,
                    crate::leanh::lean_box(0),
                );
                v___y_8518_ = v___x_8547_;
                state = 1;
                continue;
            }
            5 => {
                v___x_8565_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_8566_ = lean_nat_dec_eq(v_maxRecDepth_8552_, v___x_8565_);
                if v___x_8566_ == 0 {
                    v___x_8567_ = lean_nat_dec_eq(v_currRecDepth_8551_, v_maxRecDepth_8552_);
                    if v___x_8567_ == 0 {
                        crate::leanh::lean_inc(v_ref_8553_);
                        v___y_8528_ = v_cancelTk_x3f_8561_;
                        v___y_8529_ = v_ref_8553_;
                        v___y_8530_ = v_diag_8560_;
                        v___y_8531_ = v_suppressElabErrors_8562_;
                        v___y_8532_ = v_inheritedTraceOptions_8563_;
                        v___y_8533_ = v_quotContext_8558_;
                        v___y_8534_ = v_initHeartbeats_8556_;
                        v___y_8535_ = v_openDecls_8555_;
                        v___y_8536_ = v_currRecDepth_8551_;
                        v___y_8537_ = v_fileName_8548_;
                        v___y_8538_ = v_maxRecDepth_8552_;
                        v___y_8539_ = v_currNamespace_8554_;
                        v___y_8540_ = v_currMacroScope_8559_;
                        v___y_8541_ = v_fileMap_8549_;
                        v___y_8542_ = v_options_8550_;
                        v___y_8543_ = v_maxHeartbeats_8557_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_x_8512_);
                        crate::leanh::lean_inc(v_ref_8553_);
                        v___x_8568_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg(v_ref_8553_);
                        v___y_8518_ = v___x_8568_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_ref_8553_);
                    v___y_8528_ = v_cancelTk_x3f_8561_;
                    v___y_8529_ = v_ref_8553_;
                    v___y_8530_ = v_diag_8560_;
                    v___y_8531_ = v_suppressElabErrors_8562_;
                    v___y_8532_ = v_inheritedTraceOptions_8563_;
                    v___y_8533_ = v_quotContext_8558_;
                    v___y_8534_ = v_initHeartbeats_8556_;
                    v___y_8535_ = v_openDecls_8555_;
                    v___y_8536_ = v_currRecDepth_8551_;
                    v___y_8537_ = v_fileName_8548_;
                    v___y_8538_ = v_maxRecDepth_8552_;
                    v___y_8539_ = v_currNamespace_8554_;
                    v___y_8540_ = v_currMacroScope_8559_;
                    v___y_8541_ = v_fileMap_8549_;
                    v___y_8542_ = v_options_8550_;
                    v___y_8543_ = v_maxHeartbeats_8557_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                if v_isShared_8575_ == 0 {
                    v___x_8577_ = v___x_8574_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8578_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8578_, 0, v_a_8572_);
                    v___x_8577_ = v_reuseFailAlloc_8578_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_8577_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg___boxed(
    mut v_x_8580_: *mut crate::leanh::LeanObject,
    mut v___y_8581_: *mut crate::leanh::LeanObject,
    mut v___y_8582_: *mut crate::leanh::LeanObject,
    mut v___y_8583_: *mut crate::leanh::LeanObject,
    mut v___y_8584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8585_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg(v_x_8580_, v___y_8581_, v___y_8582_, v___y_8583_);
    crate::leanh::lean_dec(v___y_8583_);
    crate::leanh::lean_dec_ref(v___y_8582_);
    crate::leanh::lean_dec(v___y_8581_);
    return v_res_8585_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(
    mut v_00_u03b1_8586_: *mut crate::leanh::LeanObject,
    mut v_x_8587_: *mut crate::leanh::LeanObject,
    mut v___y_8588_: *mut crate::leanh::LeanObject,
    mut v___y_8589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8591_ = crate::leanh::lean_apply_1(v_x_8587_, crate::leanh::lean_box(0));
    v___x_8592_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_8592_, 0, v___x_8591_);
    return v___x_8592_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0___boxed(
    mut v_00_u03b1_8593_: *mut crate::leanh::LeanObject,
    mut v_x_8594_: *mut crate::leanh::LeanObject,
    mut v___y_8595_: *mut crate::leanh::LeanObject,
    mut v___y_8596_: *mut crate::leanh::LeanObject,
    mut v___y_8597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8598_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(v_00_u03b1_8593_, v_x_8594_, v___y_8595_, v___y_8596_);
    crate::leanh::lean_dec(v___y_8596_);
    crate::leanh::lean_dec_ref(v___y_8595_);
    return v_res_8598_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(
    mut v_pre_8599_: *mut crate::leanh::LeanObject,
    mut v_post_8600_: *mut crate::leanh::LeanObject,
    mut v_sz_8601_: usize,
    mut v_i_8602_: usize,
    mut v_bs_8603_: *mut crate::leanh::LeanObject,
    mut v___y_8604_: *mut crate::leanh::LeanObject,
    mut v___y_8605_: *mut crate::leanh::LeanObject,
    mut v___y_8606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8608_: u8 = 0;
    let mut v___x_8609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_8614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8615_: usize = 0;
    let mut v___x_8616_: usize = 0;
    let mut v___x_8617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8622_: u8 = 0;
    let mut v___x_8624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8626_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8608_ = lean_usize_dec_lt(v_i_8602_, v_sz_8601_);
                if v___x_8608_ == 0 {
                    crate::leanh::lean_dec_ref(v_post_8600_);
                    crate::leanh::lean_dec_ref(v_pre_8599_);
                    v___x_8609_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_8609_, 0, v_bs_8603_);
                    return v___x_8609_;
                } else {
                    v_v_8610_ = lean_array_uget_borrowed(v_bs_8603_, v_i_8602_);
                    crate::leanh::lean_inc(v_v_8610_);
                    crate::leanh::lean_inc_ref(v_post_8600_);
                    crate::leanh::lean_inc_ref(v_pre_8599_);
                    v___x_8611_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_8599_, v_post_8600_, v_v_8610_, v___y_8604_, v___y_8605_, v___y_8606_);
                    if crate::leanh::lean_obj_tag(v___x_8611_) == 0 {
                        v_a_8612_ = crate::leanh::lean_ctor_get(v___x_8611_, 0);
                        crate::leanh::lean_inc(v_a_8612_);
                        crate::leanh::lean_dec_ref_known(v___x_8611_, 1);
                        v___x_8613_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_8614_ = lean_array_uset(v_bs_8603_, v_i_8602_, v___x_8613_);
                        v___x_8615_ = 1usize;
                        v___x_8616_ = lean_usize_add(v_i_8602_, v___x_8615_);
                        v___x_8617_ = lean_array_uset(v_bs_x27_8614_, v_i_8602_, v_a_8612_);
                        v_i_8602_ = v___x_8616_;
                        v_bs_8603_ = v___x_8617_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_8603_);
                        crate::leanh::lean_dec_ref(v_post_8600_);
                        crate::leanh::lean_dec_ref(v_pre_8599_);
                        v_a_8619_ = crate::leanh::lean_ctor_get(v___x_8611_, 0);
                        v_isSharedCheck_8626_ =
                            (!crate::leanh::lean_is_exclusive(v___x_8611_)) as u8;
                        if v_isSharedCheck_8626_ == 0 {
                            v___x_8621_ = v___x_8611_;
                            v_isShared_8622_ = v_isSharedCheck_8626_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_8619_);
                            crate::leanh::lean_dec(v___x_8611_);
                            v___x_8621_ = crate::leanh::lean_box(0);
                            v_isShared_8622_ = v_isSharedCheck_8626_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_8622_ == 0 {
                    v___x_8624_ = v___x_8621_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8625_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8625_, 0, v_a_8619_);
                    v___x_8624_ = v_reuseFailAlloc_8625_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8624_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(
    mut v_pre_8627_: *mut crate::leanh::LeanObject,
    mut v_post_8628_: *mut crate::leanh::LeanObject,
    mut v_x_8629_: *mut crate::leanh::LeanObject,
    mut v_x_8630_: *mut crate::leanh::LeanObject,
    mut v_x_8631_: *mut crate::leanh::LeanObject,
    mut v___y_8632_: *mut crate::leanh::LeanObject,
    mut v___y_8633_: *mut crate::leanh::LeanObject,
    mut v___y_8634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_8636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_8637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_8644_: usize = 0;
    let mut v___x_8645_: usize = 0;
    let mut v___x_8646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8653_: u8 = 0;
    let mut v___x_8655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8657_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_8629_) == 5 {
                    v_fn_8636_ = crate::leanh::lean_ctor_get(v_x_8629_, 0);
                    crate::leanh::lean_inc_ref(v_fn_8636_);
                    v_arg_8637_ = crate::leanh::lean_ctor_get(v_x_8629_, 1);
                    crate::leanh::lean_inc_ref(v_arg_8637_);
                    crate::leanh::lean_dec_ref_known(v_x_8629_, 2);
                    v___x_8638_ = lean_array_set(v_x_8630_, v_x_8631_, v_arg_8637_);
                    v___x_8639_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_8640_ = lean_nat_sub(v_x_8631_, v___x_8639_);
                    crate::leanh::lean_dec(v_x_8631_);
                    v_x_8629_ = v_fn_8636_;
                    v_x_8630_ = v___x_8638_;
                    v_x_8631_ = v___x_8640_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_8631_);
                    crate::leanh::lean_inc_ref(v_post_8628_);
                    crate::leanh::lean_inc_ref(v_pre_8627_);
                    v___x_8642_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_8627_, v_post_8628_, v_x_8629_, v___y_8632_, v___y_8633_, v___y_8634_);
                    if crate::leanh::lean_obj_tag(v___x_8642_) == 0 {
                        v_a_8643_ = crate::leanh::lean_ctor_get(v___x_8642_, 0);
                        crate::leanh::lean_inc(v_a_8643_);
                        crate::leanh::lean_dec_ref_known(v___x_8642_, 1);
                        v_sz_8644_ = lean_array_size(v_x_8630_);
                        v___x_8645_ = 0usize;
                        crate::leanh::lean_inc_ref(v_post_8628_);
                        crate::leanh::lean_inc_ref(v_pre_8627_);
                        v___x_8646_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(v_pre_8627_, v_post_8628_, v_sz_8644_, v___x_8645_, v_x_8630_, v___y_8632_, v___y_8633_, v___y_8634_);
                        if crate::leanh::lean_obj_tag(v___x_8646_) == 0 {
                            v_a_8647_ = crate::leanh::lean_ctor_get(v___x_8646_, 0);
                            crate::leanh::lean_inc(v_a_8647_);
                            crate::leanh::lean_dec_ref_known(v___x_8646_, 1);
                            v___x_8648_ = l_Lean_mkAppN(v_a_8643_, v_a_8647_);
                            crate::leanh::lean_dec(v_a_8647_);
                            v___x_8649_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_8627_, v_post_8628_, v___x_8648_, v___y_8632_, v___y_8633_, v___y_8634_);
                            return v___x_8649_;
                        } else {
                            crate::leanh::lean_dec(v_a_8643_);
                            crate::leanh::lean_dec_ref(v_post_8628_);
                            crate::leanh::lean_dec_ref(v_pre_8627_);
                            v_a_8650_ = crate::leanh::lean_ctor_get(v___x_8646_, 0);
                            v_isSharedCheck_8657_ =
                                (!crate::leanh::lean_is_exclusive(v___x_8646_)) as u8;
                            if v_isSharedCheck_8657_ == 0 {
                                v___x_8652_ = v___x_8646_;
                                v_isShared_8653_ = v_isSharedCheck_8657_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_8650_);
                                crate::leanh::lean_dec(v___x_8646_);
                                v___x_8652_ = crate::leanh::lean_box(0);
                                v_isShared_8653_ = v_isSharedCheck_8657_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_8630_);
                        crate::leanh::lean_dec_ref(v_post_8628_);
                        crate::leanh::lean_dec_ref(v_pre_8627_);
                        return v___x_8642_;
                    }
                }
            }
            1 => {
                if v_isShared_8653_ == 0 {
                    v___x_8655_ = v___x_8652_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8656_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8656_, 0, v_a_8650_);
                    v___x_8655_ = v_reuseFailAlloc_8656_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8655_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1(
    mut v___x_8658_: *mut crate::leanh::LeanObject,
    mut v_pre_8659_: *mut crate::leanh::LeanObject,
    mut v_e_8660_: *mut crate::leanh::LeanObject,
    mut v_post_8661_: *mut crate::leanh::LeanObject,
    mut v___y_8662_: *mut crate::leanh::LeanObject,
    mut v___y_8663_: *mut crate::leanh::LeanObject,
    mut v___y_8664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_8667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8670_: u8 = 0;
    let mut v___y_8671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8674_: u8 = 0;
    let mut v___x_8675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8677_: usize = 0;
    let mut v___x_8678_: usize = 0;
    let mut v___x_8679_: u8 = 0;
    let mut v___x_8680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8688_: u8 = 0;
    let mut v___y_8689_: u8 = 0;
    let mut v___x_8690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8692_: u8 = 0;
    let mut v___x_8693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8700_: u8 = 0;
    let mut v___y_8701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8702_: u8 = 0;
    let mut v___x_8703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8705_: u8 = 0;
    let mut v___x_8706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8714_: u8 = 0;
    let mut v___y_8716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_8717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_8718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_8719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_8720_: u8 = 0;
    let mut v___x_8721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8725_: usize = 0;
    let mut v___x_8726_: usize = 0;
    let mut v___x_8727_: u8 = 0;
    let mut v___x_8728_: usize = 0;
    let mut v___x_8729_: usize = 0;
    let mut v___x_8730_: u8 = 0;
    let mut v_binderName_8731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_8732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_8733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_8734_: u8 = 0;
    let mut v___x_8735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8739_: usize = 0;
    let mut v___x_8740_: usize = 0;
    let mut v___x_8741_: u8 = 0;
    let mut v___x_8742_: usize = 0;
    let mut v___x_8743_: usize = 0;
    let mut v___x_8744_: u8 = 0;
    let mut v_declName_8745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_8746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_8747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_8748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_8749_: u8 = 0;
    let mut v___x_8750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8756_: usize = 0;
    let mut v___x_8757_: usize = 0;
    let mut v___x_8758_: u8 = 0;
    let mut v___x_8759_: usize = 0;
    let mut v___x_8760_: usize = 0;
    let mut v___x_8761_: u8 = 0;
    let mut v_dummy_8762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_8763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_8768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_8769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8772_: usize = 0;
    let mut v___x_8773_: usize = 0;
    let mut v___x_8774_: u8 = 0;
    let mut v___x_8775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_8778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_8779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_8780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8783_: usize = 0;
    let mut v___x_8784_: usize = 0;
    let mut v___x_8785_: u8 = 0;
    let mut v___x_8786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_8790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_8794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_8798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8800_: u8 = 0;
    let mut v_a_8801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8804_: u8 = 0;
    let mut v___x_8806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8808_: u8 = 0;
    let mut v_a_8809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8812_: u8 = 0;
    let mut v___x_8814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8816_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8709_ = l_Lean_Core_checkSystem(v___x_8658_, v___y_8663_, v___y_8664_);
                if crate::leanh::lean_obj_tag(v___x_8709_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_8709_, 1);
                    crate::leanh::lean_inc_ref(v_pre_8659_);
                    crate::leanh::lean_inc(v___y_8664_);
                    crate::leanh::lean_inc_ref(v___y_8663_);
                    crate::leanh::lean_inc_ref(v_e_8660_);
                    v___x_8710_ = crate::leanh::lean_apply_4(
                        v_pre_8659_,
                        v_e_8660_,
                        v___y_8663_,
                        v___y_8664_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_8710_) == 0 {
                        v_a_8711_ = crate::leanh::lean_ctor_get(v___x_8710_, 0);
                        v_isSharedCheck_8800_ =
                            (!crate::leanh::lean_is_exclusive(v___x_8710_)) as u8;
                        if v_isSharedCheck_8800_ == 0 {
                            v___x_8713_ = v___x_8710_;
                            v_isShared_8714_ = v_isSharedCheck_8800_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_8711_);
                            crate::leanh::lean_dec(v___x_8710_);
                            v___x_8713_ = crate::leanh::lean_box(0);
                            v_isShared_8714_ = v_isSharedCheck_8800_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_post_8661_);
                        crate::leanh::lean_dec_ref(v_e_8660_);
                        crate::leanh::lean_dec_ref(v_pre_8659_);
                        v_a_8801_ = crate::leanh::lean_ctor_get(v___x_8710_, 0);
                        v_isSharedCheck_8808_ =
                            (!crate::leanh::lean_is_exclusive(v___x_8710_)) as u8;
                        if v_isSharedCheck_8808_ == 0 {
                            v___x_8803_ = v___x_8710_;
                            v_isShared_8804_ = v_isSharedCheck_8808_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_8801_);
                            crate::leanh::lean_dec(v___x_8710_);
                            v___x_8803_ = crate::leanh::lean_box(0);
                            v_isShared_8804_ = v_isSharedCheck_8808_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_post_8661_);
                    crate::leanh::lean_dec_ref(v_e_8660_);
                    crate::leanh::lean_dec_ref(v_pre_8659_);
                    v_a_8809_ = crate::leanh::lean_ctor_get(v___x_8709_, 0);
                    v_isSharedCheck_8816_ = (!crate::leanh::lean_is_exclusive(v___x_8709_)) as u8;
                    if v_isSharedCheck_8816_ == 0 {
                        v___x_8811_ = v___x_8709_;
                        v_isShared_8812_ = v_isSharedCheck_8816_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8809_);
                        crate::leanh::lean_dec(v___x_8709_);
                        v___x_8811_ = crate::leanh::lean_box(0);
                        v_isShared_8812_ = v_isSharedCheck_8816_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_8674_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_8672_);
                    crate::leanh::lean_dec_ref(v___y_8667_);
                    v___x_8675_ = l_Lean_Expr_letE___override(
                        v___y_8668_,
                        v___y_8671_,
                        v___y_8673_,
                        v___y_8669_,
                        v___y_8670_,
                    );
                    v___x_8676_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_8659_, v_post_8661_, v___x_8675_, v___y_8662_, v___y_8663_, v___y_8664_);
                    return v___x_8676_;
                } else {
                    v___x_8677_ = lean_ptr_addr(v___y_8667_);
                    crate::leanh::lean_dec_ref(v___y_8667_);
                    v___x_8678_ = lean_ptr_addr(v___y_8669_);
                    v___x_8679_ = lean_usize_dec_eq(v___x_8677_, v___x_8678_);
                    if v___x_8679_ == 0 {
                        crate::leanh::lean_dec_ref(v___y_8672_);
                        v___x_8680_ = l_Lean_Expr_letE___override(
                            v___y_8668_,
                            v___y_8671_,
                            v___y_8673_,
                            v___y_8669_,
                            v___y_8670_,
                        );
                        v___x_8681_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_8659_, v_post_8661_, v___x_8680_, v___y_8662_, v___y_8663_, v___y_8664_);
                        return v___x_8681_;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_8673_);
                        crate::leanh::lean_dec_ref(v___y_8671_);
                        crate::leanh::lean_dec_ref(v___y_8669_);
                        crate::leanh::lean_dec(v___y_8668_);
                        v___x_8682_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_8659_, v_post_8661_, v___y_8672_, v___y_8662_, v___y_8663_, v___y_8664_);
                        return v___x_8682_;
                    }
                }
            }
            2 => {
                if v___y_8689_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_8684_);
                    v___x_8690_ = l_Lean_Expr_lam___override(
                        v___y_8686_,
                        v___y_8687_,
                        v___y_8685_,
                        v___y_8688_,
                    );
                    v___x_8691_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_8659_, v_post_8661_, v___x_8690_, v___y_8662_, v___y_8663_, v___y_8664_);
                    return v___x_8691_;
                } else {
                    v___x_8692_ = l_Lean_instBEqBinderInfo_beq(v___y_8688_, v___y_8688_);
                    if v___x_8692_ == 0 {
                        crate::leanh::lean_dec_ref(v___y_8684_);
                        v___x_8693_ = l_Lean_Expr_lam___override(
                            v___y_8686_,
                            v___y_8687_,
                            v___y_8685_,
                            v___y_8688_,
                        );
                        v___x_8694_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_8659_, v_post_8661_, v___x_8693_, v___y_8662_, v___y_8663_, v___y_8664_);
                        return v___x_8694_;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_8687_);
                        crate::leanh::lean_dec(v___y_8686_);
                        crate::leanh::lean_dec_ref(v___y_8685_);
                        v___x_8695_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_8659_, v_post_8661_, v___y_8684_, v___y_8662_, v___y_8663_, v___y_8664_);
                        return v___x_8695_;
                    }
                }
            }
            3 => {
                if v___y_8702_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_8698_);
                    v___x_8703_ = l_Lean_Expr_forallE___override(
                        v___y_8699_,
                        v___y_8697_,
                        v___y_8701_,
                        v___y_8700_,
                    );
                    v___x_8704_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_8659_, v_post_8661_, v___x_8703_, v___y_8662_, v___y_8663_, v___y_8664_);
                    return v___x_8704_;
                } else {
                    v___x_8705_ = l_Lean_instBEqBinderInfo_beq(v___y_8700_, v___y_8700_);
                    if v___x_8705_ == 0 {
                        crate::leanh::lean_dec_ref(v___y_8698_);
                        v___x_8706_ = l_Lean_Expr_forallE___override(
                            v___y_8699_,
                            v___y_8697_,
                            v___y_8701_,
                            v___y_8700_,
                        );
                        v___x_8707_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_8659_, v_post_8661_, v___x_8706_, v___y_8662_, v___y_8663_, v___y_8664_);
                        return v___x_8707_;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_8701_);
                        crate::leanh::lean_dec(v___y_8699_);
                        crate::leanh::lean_dec_ref(v___y_8697_);
                        v___x_8708_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_8659_, v_post_8661_, v___y_8698_, v___y_8662_, v___y_8663_, v___y_8664_);
                        return v___x_8708_;
                    }
                }
            }
            4 => match crate::leanh::lean_obj_tag(v_a_8711_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_post_8661_);
                    crate::leanh::lean_dec_ref(v_e_8660_);
                    crate::leanh::lean_dec_ref(v_pre_8659_);
                    v_e_8790_ = crate::leanh::lean_ctor_get(v_a_8711_, 0);
                    crate::leanh::lean_inc_ref(v_e_8790_);
                    crate::leanh::lean_dec_ref_known(v_a_8711_, 1);
                    if v_isShared_8714_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8713_, 0, v_e_8790_);
                        v___x_8792_ = v___x_8713_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_8793_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8793_, 0, v_e_8790_);
                        v___x_8792_ = v_reuseFailAlloc_8793_;
                        state = 6;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_8713_);
                    crate::leanh::lean_dec_ref(v_e_8660_);
                    v_e_8794_ = crate::leanh::lean_ctor_get(v_a_8711_, 0);
                    crate::leanh::lean_inc_ref(v_e_8794_);
                    crate::leanh::lean_dec_ref_known(v_a_8711_, 1);
                    crate::leanh::lean_inc_ref(v_post_8661_);
                    crate::leanh::lean_inc_ref(v_pre_8659_);
                    v___x_8795_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_8659_, v_post_8661_, v_e_8794_, v___y_8662_, v___y_8663_, v___y_8664_);
                    if crate::leanh::lean_obj_tag(v___x_8795_) == 0 {
                        v_a_8796_ = crate::leanh::lean_ctor_get(v___x_8795_, 0);
                        crate::leanh::lean_inc(v_a_8796_);
                        crate::leanh::lean_dec_ref_known(v___x_8795_, 1);
                        v___x_8797_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_8659_, v_post_8661_, v_a_8796_, v___y_8662_, v___y_8663_, v___y_8664_);
                        return v___x_8797_;
                    } else {
                        crate::leanh::lean_dec_ref(v_post_8661_);
                        crate::leanh::lean_dec_ref(v_pre_8659_);
                        return v___x_8795_;
                    }
                }
                _ => {
                    crate::leanh::lean_del_object(v___x_8713_);
                    v_e_x3f_8798_ = crate::leanh::lean_ctor_get(v_a_8711_, 0);
                    crate::leanh::lean_inc(v_e_x3f_8798_);
                    crate::leanh::lean_dec_ref_known(v_a_8711_, 1);
                    if crate::leanh::lean_obj_tag(v_e_x3f_8798_) == 0 {
                        v___y_8716_ = v_e_8660_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_e_8660_);
                        v_val_8799_ = crate::leanh::lean_ctor_get(v_e_x3f_8798_, 0);
                        crate::leanh::lean_inc(v_val_8799_);
                        crate::leanh::lean_dec_ref_known(v_e_x3f_8798_, 1);
                        v___y_8716_ = v_val_8799_;
                        state = 5;
                        continue;
                    }
                }
            },
            5 => match crate::leanh::lean_obj_tag(v___y_8716_) {
                7 => {
                    v_binderName_8717_ = crate::leanh::lean_ctor_get(v___y_8716_, 0);
                    crate::leanh::lean_inc(v_binderName_8717_);
                    v_binderType_8718_ = crate::leanh::lean_ctor_get(v___y_8716_, 1);
                    v_body_8719_ = crate::leanh::lean_ctor_get(v___y_8716_, 2);
                    v_binderInfo_8720_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_8716_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc_ref(v_binderType_8718_);
                    crate::leanh::lean_inc_ref(v_post_8661_);
                    crate::leanh::lean_inc_ref(v_pre_8659_);
                    v___x_8721_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_8659_, v_post_8661_, v_binderType_8718_, v___y_8662_, v___y_8663_, v___y_8664_);
                    if crate::leanh::lean_obj_tag(v___x_8721_) == 0 {
                        v_a_8722_ = crate::leanh::lean_ctor_get(v___x_8721_, 0);
                        crate::leanh::lean_inc(v_a_8722_);
                        crate::leanh::lean_dec_ref_known(v___x_8721_, 1);
                        crate::leanh::lean_inc_ref(v_body_8719_);
                        crate::leanh::lean_inc_ref(v_post_8661_);
                        crate::leanh::lean_inc_ref(v_pre_8659_);
                        v___x_8723_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_8659_, v_post_8661_, v_body_8719_, v___y_8662_, v___y_8663_, v___y_8664_);
                        if crate::leanh::lean_obj_tag(v___x_8723_) == 0 {
                            v_a_8724_ = crate::leanh::lean_ctor_get(v___x_8723_, 0);
                            crate::leanh::lean_inc(v_a_8724_);
                            crate::leanh::lean_dec_ref_known(v___x_8723_, 1);
                            v___x_8725_ = lean_ptr_addr(v_binderType_8718_);
                            v___x_8726_ = lean_ptr_addr(v_a_8722_);
                            v___x_8727_ = lean_usize_dec_eq(v___x_8725_, v___x_8726_);
                            if v___x_8727_ == 0 {
                                v___y_8697_ = v_a_8722_;
                                v___y_8698_ = v___y_8716_;
                                v___y_8699_ = v_binderName_8717_;
                                v___y_8700_ = v_binderInfo_8720_;
                                v___y_8701_ = v_a_8724_;
                                v___y_8702_ = v___x_8727_;
                                state = 3;
                                continue;
                            } else {
                                v___x_8728_ = lean_ptr_addr(v_body_8719_);
                                v___x_8729_ = lean_ptr_addr(v_a_8724_);
                                v___x_8730_ = lean_usize_dec_eq(v___x_8728_, v___x_8729_);
                                v___y_8697_ = v_a_8722_;
                                v___y_8698_ = v___y_8716_;
                                v___y_8699_ = v_binderName_8717_;
                                v___y_8700_ = v_binderInfo_8720_;
                                v___y_8701_ = v_a_8724_;
                                v___y_8702_ = v___x_8730_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_8722_);
                            crate::leanh::lean_dec_ref_known(v___y_8716_, 3);
                            crate::leanh::lean_dec(v_binderName_8717_);
                            crate::leanh::lean_dec_ref(v_post_8661_);
                            crate::leanh::lean_dec_ref(v_pre_8659_);
                            return v___x_8723_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_binderName_8717_);
                        crate::leanh::lean_dec_ref_known(v___y_8716_, 3);
                        crate::leanh::lean_dec_ref(v_post_8661_);
                        crate::leanh::lean_dec_ref(v_pre_8659_);
                        return v___x_8721_;
                    }
                }
                6 => {
                    v_binderName_8731_ = crate::leanh::lean_ctor_get(v___y_8716_, 0);
                    crate::leanh::lean_inc(v_binderName_8731_);
                    v_binderType_8732_ = crate::leanh::lean_ctor_get(v___y_8716_, 1);
                    v_body_8733_ = crate::leanh::lean_ctor_get(v___y_8716_, 2);
                    v_binderInfo_8734_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_8716_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc_ref(v_binderType_8732_);
                    crate::leanh::lean_inc_ref(v_post_8661_);
                    crate::leanh::lean_inc_ref(v_pre_8659_);
                    v___x_8735_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_8659_, v_post_8661_, v_binderType_8732_, v___y_8662_, v___y_8663_, v___y_8664_);
                    if crate::leanh::lean_obj_tag(v___x_8735_) == 0 {
                        v_a_8736_ = crate::leanh::lean_ctor_get(v___x_8735_, 0);
                        crate::leanh::lean_inc(v_a_8736_);
                        crate::leanh::lean_dec_ref_known(v___x_8735_, 1);
                        crate::leanh::lean_inc_ref(v_body_8733_);
                        crate::leanh::lean_inc_ref(v_post_8661_);
                        crate::leanh::lean_inc_ref(v_pre_8659_);
                        v___x_8737_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_8659_, v_post_8661_, v_body_8733_, v___y_8662_, v___y_8663_, v___y_8664_);
                        if crate::leanh::lean_obj_tag(v___x_8737_) == 0 {
                            v_a_8738_ = crate::leanh::lean_ctor_get(v___x_8737_, 0);
                            crate::leanh::lean_inc(v_a_8738_);
                            crate::leanh::lean_dec_ref_known(v___x_8737_, 1);
                            v___x_8739_ = lean_ptr_addr(v_binderType_8732_);
                            v___x_8740_ = lean_ptr_addr(v_a_8736_);
                            v___x_8741_ = lean_usize_dec_eq(v___x_8739_, v___x_8740_);
                            if v___x_8741_ == 0 {
                                v___y_8684_ = v___y_8716_;
                                v___y_8685_ = v_a_8738_;
                                v___y_8686_ = v_binderName_8731_;
                                v___y_8687_ = v_a_8736_;
                                v___y_8688_ = v_binderInfo_8734_;
                                v___y_8689_ = v___x_8741_;
                                state = 2;
                                continue;
                            } else {
                                v___x_8742_ = lean_ptr_addr(v_body_8733_);
                                v___x_8743_ = lean_ptr_addr(v_a_8738_);
                                v___x_8744_ = lean_usize_dec_eq(v___x_8742_, v___x_8743_);
                                v___y_8684_ = v___y_8716_;
                                v___y_8685_ = v_a_8738_;
                                v___y_8686_ = v_binderName_8731_;
                                v___y_8687_ = v_a_8736_;
                                v___y_8688_ = v_binderInfo_8734_;
                                v___y_8689_ = v___x_8744_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_8736_);
                            crate::leanh::lean_dec(v_binderName_8731_);
                            crate::leanh::lean_dec_ref_known(v___y_8716_, 3);
                            crate::leanh::lean_dec_ref(v_post_8661_);
                            crate::leanh::lean_dec_ref(v_pre_8659_);
                            return v___x_8737_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_8716_, 3);
                        crate::leanh::lean_dec(v_binderName_8731_);
                        crate::leanh::lean_dec_ref(v_post_8661_);
                        crate::leanh::lean_dec_ref(v_pre_8659_);
                        return v___x_8735_;
                    }
                }
                8 => {
                    v_declName_8745_ = crate::leanh::lean_ctor_get(v___y_8716_, 0);
                    crate::leanh::lean_inc(v_declName_8745_);
                    v_type_8746_ = crate::leanh::lean_ctor_get(v___y_8716_, 1);
                    v_value_8747_ = crate::leanh::lean_ctor_get(v___y_8716_, 2);
                    v_body_8748_ = crate::leanh::lean_ctor_get(v___y_8716_, 3);
                    crate::leanh::lean_inc_ref(v_body_8748_);
                    v_nondep_8749_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_8716_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    crate::leanh::lean_inc_ref(v_type_8746_);
                    crate::leanh::lean_inc_ref(v_post_8661_);
                    crate::leanh::lean_inc_ref(v_pre_8659_);
                    v___x_8750_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_8659_, v_post_8661_, v_type_8746_, v___y_8662_, v___y_8663_, v___y_8664_);
                    if crate::leanh::lean_obj_tag(v___x_8750_) == 0 {
                        v_a_8751_ = crate::leanh::lean_ctor_get(v___x_8750_, 0);
                        crate::leanh::lean_inc(v_a_8751_);
                        crate::leanh::lean_dec_ref_known(v___x_8750_, 1);
                        crate::leanh::lean_inc_ref(v_value_8747_);
                        crate::leanh::lean_inc_ref(v_post_8661_);
                        crate::leanh::lean_inc_ref(v_pre_8659_);
                        v___x_8752_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_8659_, v_post_8661_, v_value_8747_, v___y_8662_, v___y_8663_, v___y_8664_);
                        if crate::leanh::lean_obj_tag(v___x_8752_) == 0 {
                            v_a_8753_ = crate::leanh::lean_ctor_get(v___x_8752_, 0);
                            crate::leanh::lean_inc(v_a_8753_);
                            crate::leanh::lean_dec_ref_known(v___x_8752_, 1);
                            crate::leanh::lean_inc_ref(v_body_8748_);
                            crate::leanh::lean_inc_ref(v_post_8661_);
                            crate::leanh::lean_inc_ref(v_pre_8659_);
                            v___x_8754_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_8659_, v_post_8661_, v_body_8748_, v___y_8662_, v___y_8663_, v___y_8664_);
                            if crate::leanh::lean_obj_tag(v___x_8754_) == 0 {
                                v_a_8755_ = crate::leanh::lean_ctor_get(v___x_8754_, 0);
                                crate::leanh::lean_inc(v_a_8755_);
                                crate::leanh::lean_dec_ref_known(v___x_8754_, 1);
                                v___x_8756_ = lean_ptr_addr(v_type_8746_);
                                v___x_8757_ = lean_ptr_addr(v_a_8751_);
                                v___x_8758_ = lean_usize_dec_eq(v___x_8756_, v___x_8757_);
                                if v___x_8758_ == 0 {
                                    v___y_8667_ = v_body_8748_;
                                    v___y_8668_ = v_declName_8745_;
                                    v___y_8669_ = v_a_8755_;
                                    v___y_8670_ = v_nondep_8749_;
                                    v___y_8671_ = v_a_8751_;
                                    v___y_8672_ = v___y_8716_;
                                    v___y_8673_ = v_a_8753_;
                                    v___y_8674_ = v___x_8758_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_8759_ = lean_ptr_addr(v_value_8747_);
                                    v___x_8760_ = lean_ptr_addr(v_a_8753_);
                                    v___x_8761_ = lean_usize_dec_eq(v___x_8759_, v___x_8760_);
                                    v___y_8667_ = v_body_8748_;
                                    v___y_8668_ = v_declName_8745_;
                                    v___y_8669_ = v_a_8755_;
                                    v___y_8670_ = v_nondep_8749_;
                                    v___y_8671_ = v_a_8751_;
                                    v___y_8672_ = v___y_8716_;
                                    v___y_8673_ = v_a_8753_;
                                    v___y_8674_ = v___x_8761_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_8753_);
                                crate::leanh::lean_dec(v_a_8751_);
                                crate::leanh::lean_dec_ref(v_body_8748_);
                                crate::leanh::lean_dec_ref_known(v___y_8716_, 4);
                                crate::leanh::lean_dec(v_declName_8745_);
                                crate::leanh::lean_dec_ref(v_post_8661_);
                                crate::leanh::lean_dec_ref(v_pre_8659_);
                                return v___x_8754_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_8751_);
                            crate::leanh::lean_dec_ref(v_body_8748_);
                            crate::leanh::lean_dec_ref_known(v___y_8716_, 4);
                            crate::leanh::lean_dec(v_declName_8745_);
                            crate::leanh::lean_dec_ref(v_post_8661_);
                            crate::leanh::lean_dec_ref(v_pre_8659_);
                            return v___x_8752_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_body_8748_);
                        crate::leanh::lean_dec_ref_known(v___y_8716_, 4);
                        crate::leanh::lean_dec(v_declName_8745_);
                        crate::leanh::lean_dec_ref(v_post_8661_);
                        crate::leanh::lean_dec_ref(v_pre_8659_);
                        return v___x_8750_;
                    }
                }
                5 => {
                    v_dummy_8762_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1_once), _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1);
                    v_nargs_8763_ = l_Lean_Expr_getAppNumArgs(v___y_8716_);
                    crate::leanh::lean_inc(v_nargs_8763_);
                    v___x_8764_ = lean_mk_array(v_nargs_8763_, v_dummy_8762_);
                    v___x_8765_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_8766_ = lean_nat_sub(v_nargs_8763_, v___x_8765_);
                    crate::leanh::lean_dec(v_nargs_8763_);
                    v___x_8767_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_8659_, v_post_8661_, v___y_8716_, v___x_8764_, v___x_8766_, v___y_8662_, v___y_8663_, v___y_8664_);
                    return v___x_8767_;
                }
                10 => {
                    v_data_8768_ = crate::leanh::lean_ctor_get(v___y_8716_, 0);
                    v_expr_8769_ = crate::leanh::lean_ctor_get(v___y_8716_, 1);
                    crate::leanh::lean_inc_ref(v_expr_8769_);
                    crate::leanh::lean_inc_ref(v_post_8661_);
                    crate::leanh::lean_inc_ref(v_pre_8659_);
                    v___x_8770_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_8659_, v_post_8661_, v_expr_8769_, v___y_8662_, v___y_8663_, v___y_8664_);
                    if crate::leanh::lean_obj_tag(v___x_8770_) == 0 {
                        v_a_8771_ = crate::leanh::lean_ctor_get(v___x_8770_, 0);
                        crate::leanh::lean_inc(v_a_8771_);
                        crate::leanh::lean_dec_ref_known(v___x_8770_, 1);
                        v___x_8772_ = lean_ptr_addr(v_expr_8769_);
                        v___x_8773_ = lean_ptr_addr(v_a_8771_);
                        v___x_8774_ = lean_usize_dec_eq(v___x_8772_, v___x_8773_);
                        if v___x_8774_ == 0 {
                            crate::leanh::lean_inc(v_data_8768_);
                            crate::leanh::lean_dec_ref_known(v___y_8716_, 2);
                            v___x_8775_ = l_Lean_Expr_mdata___override(v_data_8768_, v_a_8771_);
                            v___x_8776_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_8659_, v_post_8661_, v___x_8775_, v___y_8662_, v___y_8663_, v___y_8664_);
                            return v___x_8776_;
                        } else {
                            crate::leanh::lean_dec(v_a_8771_);
                            v___x_8777_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_8659_, v_post_8661_, v___y_8716_, v___y_8662_, v___y_8663_, v___y_8664_);
                            return v___x_8777_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_8716_, 2);
                        crate::leanh::lean_dec_ref(v_post_8661_);
                        crate::leanh::lean_dec_ref(v_pre_8659_);
                        return v___x_8770_;
                    }
                }
                11 => {
                    v_typeName_8778_ = crate::leanh::lean_ctor_get(v___y_8716_, 0);
                    v_idx_8779_ = crate::leanh::lean_ctor_get(v___y_8716_, 1);
                    v_struct_8780_ = crate::leanh::lean_ctor_get(v___y_8716_, 2);
                    crate::leanh::lean_inc_ref(v_struct_8780_);
                    crate::leanh::lean_inc_ref(v_post_8661_);
                    crate::leanh::lean_inc_ref(v_pre_8659_);
                    v___x_8781_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_8659_, v_post_8661_, v_struct_8780_, v___y_8662_, v___y_8663_, v___y_8664_);
                    if crate::leanh::lean_obj_tag(v___x_8781_) == 0 {
                        v_a_8782_ = crate::leanh::lean_ctor_get(v___x_8781_, 0);
                        crate::leanh::lean_inc(v_a_8782_);
                        crate::leanh::lean_dec_ref_known(v___x_8781_, 1);
                        v___x_8783_ = lean_ptr_addr(v_struct_8780_);
                        v___x_8784_ = lean_ptr_addr(v_a_8782_);
                        v___x_8785_ = lean_usize_dec_eq(v___x_8783_, v___x_8784_);
                        if v___x_8785_ == 0 {
                            crate::leanh::lean_inc(v_idx_8779_);
                            crate::leanh::lean_inc(v_typeName_8778_);
                            crate::leanh::lean_dec_ref_known(v___y_8716_, 3);
                            v___x_8786_ = l_Lean_Expr_proj___override(
                                v_typeName_8778_,
                                v_idx_8779_,
                                v_a_8782_,
                            );
                            v___x_8787_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_8659_, v_post_8661_, v___x_8786_, v___y_8662_, v___y_8663_, v___y_8664_);
                            return v___x_8787_;
                        } else {
                            crate::leanh::lean_dec(v_a_8782_);
                            v___x_8788_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_8659_, v_post_8661_, v___y_8716_, v___y_8662_, v___y_8663_, v___y_8664_);
                            return v___x_8788_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_8716_, 3);
                        crate::leanh::lean_dec_ref(v_post_8661_);
                        crate::leanh::lean_dec_ref(v_pre_8659_);
                        return v___x_8781_;
                    }
                }
                _ => {
                    v___x_8789_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_8659_, v_post_8661_, v___y_8716_, v___y_8662_, v___y_8663_, v___y_8664_);
                    return v___x_8789_;
                }
            },
            6 => {
                return v___x_8792_;
            }
            7 => {
                if v_isShared_8804_ == 0 {
                    v___x_8806_ = v___x_8803_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8807_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8807_, 0, v_a_8801_);
                    v___x_8806_ = v_reuseFailAlloc_8807_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_8806_;
            }
            9 => {
                if v_isShared_8812_ == 0 {
                    v___x_8814_ = v___x_8811_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_8815_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8815_, 0, v_a_8809_);
                    v___x_8814_ = v_reuseFailAlloc_8815_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_8814_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___boxed(
    mut v___x_8817_: *mut crate::leanh::LeanObject,
    mut v_pre_8818_: *mut crate::leanh::LeanObject,
    mut v_e_8819_: *mut crate::leanh::LeanObject,
    mut v_post_8820_: *mut crate::leanh::LeanObject,
    mut v___y_8821_: *mut crate::leanh::LeanObject,
    mut v___y_8822_: *mut crate::leanh::LeanObject,
    mut v___y_8823_: *mut crate::leanh::LeanObject,
    mut v___y_8824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8825_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1(v___x_8817_, v_pre_8818_, v_e_8819_, v_post_8820_, v___y_8821_, v___y_8822_, v___y_8823_);
    crate::leanh::lean_dec(v___y_8823_);
    crate::leanh::lean_dec_ref(v___y_8822_);
    crate::leanh::lean_dec(v___y_8821_);
    return v_res_8825_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(
    mut v_pre_8826_: *mut crate::leanh::LeanObject,
    mut v_post_8827_: *mut crate::leanh::LeanObject,
    mut v_e_8828_: *mut crate::leanh::LeanObject,
    mut v_a_8829_: *mut crate::leanh::LeanObject,
    mut v___y_8830_: *mut crate::leanh::LeanObject,
    mut v___y_8831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8838_: u8 = 0;
    let mut v___x_8839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8848_: u8 = 0;
    let mut v___x_8850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8852_: u8 = 0;
    let mut v_unused_8853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8857_: u8 = 0;
    let mut v___x_8859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8861_: u8 = 0;
    let mut v_val_8862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8866_: u8 = 0;
    let mut v_a_8867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8870_: u8 = 0;
    let mut v___x_8872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8874_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_8829_);
                v___x_8833_ = crate::leanh::lean_alloc_closure(
                    l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_8833_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_8833_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_8833_, 2, v_a_8829_);
                v___x_8834_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(crate::leanh::lean_box(0), v___x_8833_, v___y_8830_, v___y_8831_);
                if crate::leanh::lean_obj_tag(v___x_8834_) == 0 {
                    v_a_8835_ = crate::leanh::lean_ctor_get(v___x_8834_, 0);
                    v_isSharedCheck_8866_ = (!crate::leanh::lean_is_exclusive(v___x_8834_)) as u8;
                    if v_isSharedCheck_8866_ == 0 {
                        v___x_8837_ = v___x_8834_;
                        v_isShared_8838_ = v_isSharedCheck_8866_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8835_);
                        crate::leanh::lean_dec(v___x_8834_);
                        v___x_8837_ = crate::leanh::lean_box(0);
                        v_isShared_8838_ = v_isSharedCheck_8866_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_8828_);
                    crate::leanh::lean_dec_ref(v_post_8827_);
                    crate::leanh::lean_dec_ref(v_pre_8826_);
                    v_a_8867_ = crate::leanh::lean_ctor_get(v___x_8834_, 0);
                    v_isSharedCheck_8874_ = (!crate::leanh::lean_is_exclusive(v___x_8834_)) as u8;
                    if v_isSharedCheck_8874_ == 0 {
                        v___x_8869_ = v___x_8834_;
                        v_isShared_8870_ = v_isSharedCheck_8874_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8867_);
                        crate::leanh::lean_dec(v___x_8834_);
                        v___x_8869_ = crate::leanh::lean_box(0);
                        v_isShared_8870_ = v_isSharedCheck_8874_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8839_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_a_8835_, v_e_8828_);
                crate::leanh::lean_dec(v_a_8835_);
                if crate::leanh::lean_obj_tag(v___x_8839_) == 0 {
                    crate::leanh::lean_del_object(v___x_8837_);
                    v___x_8840_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0;
                    crate::leanh::lean_inc_ref(v_e_8828_);
                    v___f_8841_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___boxed as *mut core::ffi::c_void, 8, 4);
                    crate::leanh::lean_closure_set(v___f_8841_, 0, v___x_8840_);
                    crate::leanh::lean_closure_set(v___f_8841_, 1, v_pre_8826_);
                    crate::leanh::lean_closure_set(v___f_8841_, 2, v_e_8828_);
                    crate::leanh::lean_closure_set(v___f_8841_, 3, v_post_8827_);
                    v___x_8842_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg(v___f_8841_, v_a_8829_, v___y_8830_, v___y_8831_);
                    if crate::leanh::lean_obj_tag(v___x_8842_) == 0 {
                        v_a_8843_ = crate::leanh::lean_ctor_get(v___x_8842_, 0);
                        crate::leanh::lean_inc_n(v_a_8843_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_8842_, 1);
                        crate::leanh::lean_inc(v_a_8829_);
                        v___f_8844_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed as *mut core::ffi::c_void, 4, 3);
                        crate::leanh::lean_closure_set(v___f_8844_, 0, v_a_8829_);
                        crate::leanh::lean_closure_set(v___f_8844_, 1, v_e_8828_);
                        crate::leanh::lean_closure_set(v___f_8844_, 2, v_a_8843_);
                        v___x_8845_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(crate::leanh::lean_box(0), v___f_8844_, v___y_8830_, v___y_8831_);
                        if crate::leanh::lean_obj_tag(v___x_8845_) == 0 {
                            v_isSharedCheck_8852_ =
                                (!crate::leanh::lean_is_exclusive(v___x_8845_)) as u8;
                            if v_isSharedCheck_8852_ == 0 {
                                v_unused_8853_ = crate::leanh::lean_ctor_get(v___x_8845_, 0);
                                crate::leanh::lean_dec(v_unused_8853_);
                                v___x_8847_ = v___x_8845_;
                                v_isShared_8848_ = v_isSharedCheck_8852_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_8845_);
                                v___x_8847_ = crate::leanh::lean_box(0);
                                v_isShared_8848_ = v_isSharedCheck_8852_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_8843_);
                            v_a_8854_ = crate::leanh::lean_ctor_get(v___x_8845_, 0);
                            v_isSharedCheck_8861_ =
                                (!crate::leanh::lean_is_exclusive(v___x_8845_)) as u8;
                            if v_isSharedCheck_8861_ == 0 {
                                v___x_8856_ = v___x_8845_;
                                v_isShared_8857_ = v_isSharedCheck_8861_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_8854_);
                                crate::leanh::lean_dec(v___x_8845_);
                                v___x_8856_ = crate::leanh::lean_box(0);
                                v_isShared_8857_ = v_isSharedCheck_8861_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_8828_);
                        return v___x_8842_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_8828_);
                    crate::leanh::lean_dec_ref(v_post_8827_);
                    crate::leanh::lean_dec_ref(v_pre_8826_);
                    v_val_8862_ = crate::leanh::lean_ctor_get(v___x_8839_, 0);
                    crate::leanh::lean_inc(v_val_8862_);
                    crate::leanh::lean_dec_ref_known(v___x_8839_, 1);
                    if v_isShared_8838_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8837_, 0, v_val_8862_);
                        v___x_8864_ = v___x_8837_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_8865_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8865_, 0, v_val_8862_);
                        v___x_8864_ = v_reuseFailAlloc_8865_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_8848_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8847_, 0, v_a_8843_);
                    v___x_8850_ = v___x_8847_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8851_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8851_, 0, v_a_8843_);
                    v___x_8850_ = v_reuseFailAlloc_8851_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_8850_;
            }
            4 => {
                if v_isShared_8857_ == 0 {
                    v___x_8859_ = v___x_8856_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8860_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8860_, 0, v_a_8854_);
                    v___x_8859_ = v_reuseFailAlloc_8860_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_8859_;
            }
            6 => {
                return v___x_8864_;
            }
            7 => {
                if v_isShared_8870_ == 0 {
                    v___x_8872_ = v___x_8869_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8873_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8873_, 0, v_a_8867_);
                    v___x_8872_ = v_reuseFailAlloc_8873_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_8872_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(
    mut v_pre_8875_: *mut crate::leanh::LeanObject,
    mut v_post_8876_: *mut crate::leanh::LeanObject,
    mut v_e_8877_: *mut crate::leanh::LeanObject,
    mut v_a_8878_: *mut crate::leanh::LeanObject,
    mut v___y_8879_: *mut crate::leanh::LeanObject,
    mut v___y_8880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8886_: u8 = 0;
    let mut v_e_8887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_8891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_8893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8901_: u8 = 0;
    let mut v_a_8902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8905_: u8 = 0;
    let mut v___x_8907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8909_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_post_8876_);
                crate::leanh::lean_inc(v___y_8880_);
                crate::leanh::lean_inc_ref(v___y_8879_);
                crate::leanh::lean_inc_ref(v_e_8877_);
                v___x_8882_ = crate::leanh::lean_apply_4(
                    v_post_8876_,
                    v_e_8877_,
                    v___y_8879_,
                    v___y_8880_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_8882_) == 0 {
                    v_a_8883_ = crate::leanh::lean_ctor_get(v___x_8882_, 0);
                    v_isSharedCheck_8901_ = (!crate::leanh::lean_is_exclusive(v___x_8882_)) as u8;
                    if v_isSharedCheck_8901_ == 0 {
                        v___x_8885_ = v___x_8882_;
                        v_isShared_8886_ = v_isSharedCheck_8901_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8883_);
                        crate::leanh::lean_dec(v___x_8882_);
                        v___x_8885_ = crate::leanh::lean_box(0);
                        v_isShared_8886_ = v_isSharedCheck_8901_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_8877_);
                    crate::leanh::lean_dec_ref(v_post_8876_);
                    crate::leanh::lean_dec_ref(v_pre_8875_);
                    v_a_8902_ = crate::leanh::lean_ctor_get(v___x_8882_, 0);
                    v_isSharedCheck_8909_ = (!crate::leanh::lean_is_exclusive(v___x_8882_)) as u8;
                    if v_isSharedCheck_8909_ == 0 {
                        v___x_8904_ = v___x_8882_;
                        v_isShared_8905_ = v_isSharedCheck_8909_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8902_);
                        crate::leanh::lean_dec(v___x_8882_);
                        v___x_8904_ = crate::leanh::lean_box(0);
                        v_isShared_8905_ = v_isSharedCheck_8909_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => match crate::leanh::lean_obj_tag(v_a_8883_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_e_8877_);
                    crate::leanh::lean_dec_ref(v_post_8876_);
                    crate::leanh::lean_dec_ref(v_pre_8875_);
                    v_e_8887_ = crate::leanh::lean_ctor_get(v_a_8883_, 0);
                    crate::leanh::lean_inc_ref(v_e_8887_);
                    crate::leanh::lean_dec_ref_known(v_a_8883_, 1);
                    if v_isShared_8886_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8885_, 0, v_e_8887_);
                        v___x_8889_ = v___x_8885_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8890_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8890_, 0, v_e_8887_);
                        v___x_8889_ = v_reuseFailAlloc_8890_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_8885_);
                    crate::leanh::lean_dec_ref(v_e_8877_);
                    v_e_8891_ = crate::leanh::lean_ctor_get(v_a_8883_, 0);
                    crate::leanh::lean_inc_ref(v_e_8891_);
                    crate::leanh::lean_dec_ref_known(v_a_8883_, 1);
                    v___x_8892_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_8875_, v_post_8876_, v_e_8891_, v_a_8878_, v___y_8879_, v___y_8880_);
                    return v___x_8892_;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_post_8876_);
                    crate::leanh::lean_dec_ref(v_pre_8875_);
                    v_e_x3f_8893_ = crate::leanh::lean_ctor_get(v_a_8883_, 0);
                    crate::leanh::lean_inc(v_e_x3f_8893_);
                    crate::leanh::lean_dec_ref_known(v_a_8883_, 1);
                    if crate::leanh::lean_obj_tag(v_e_x3f_8893_) == 0 {
                        if v_isShared_8886_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_8885_, 0, v_e_8877_);
                            v___x_8895_ = v___x_8885_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_8896_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8896_, 0, v_e_8877_);
                            v___x_8895_ = v_reuseFailAlloc_8896_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_8877_);
                        v_val_8897_ = crate::leanh::lean_ctor_get(v_e_x3f_8893_, 0);
                        crate::leanh::lean_inc(v_val_8897_);
                        crate::leanh::lean_dec_ref_known(v_e_x3f_8893_, 1);
                        if v_isShared_8886_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_8885_, 0, v_val_8897_);
                            v___x_8899_ = v___x_8885_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_8900_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8900_, 0, v_val_8897_);
                            v___x_8899_ = v_reuseFailAlloc_8900_;
                            state = 4;
                            continue;
                        }
                    }
                }
            },
            2 => {
                return v___x_8889_;
            }
            3 => {
                return v___x_8895_;
            }
            4 => {
                return v___x_8899_;
            }
            5 => {
                if v_isShared_8905_ == 0 {
                    v___x_8907_ = v___x_8904_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8908_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8908_, 0, v_a_8902_);
                    v___x_8907_ = v_reuseFailAlloc_8908_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8907_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3___boxed(
    mut v_pre_8910_: *mut crate::leanh::LeanObject,
    mut v_post_8911_: *mut crate::leanh::LeanObject,
    mut v_e_8912_: *mut crate::leanh::LeanObject,
    mut v_a_8913_: *mut crate::leanh::LeanObject,
    mut v___y_8914_: *mut crate::leanh::LeanObject,
    mut v___y_8915_: *mut crate::leanh::LeanObject,
    mut v___y_8916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8917_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_8910_, v_post_8911_, v_e_8912_, v_a_8913_, v___y_8914_, v___y_8915_);
    crate::leanh::lean_dec(v___y_8915_);
    crate::leanh::lean_dec_ref(v___y_8914_);
    crate::leanh::lean_dec(v_a_8913_);
    return v_res_8917_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2___boxed(
    mut v_pre_8918_: *mut crate::leanh::LeanObject,
    mut v_post_8919_: *mut crate::leanh::LeanObject,
    mut v_sz_8920_: *mut crate::leanh::LeanObject,
    mut v_i_8921_: *mut crate::leanh::LeanObject,
    mut v_bs_8922_: *mut crate::leanh::LeanObject,
    mut v___y_8923_: *mut crate::leanh::LeanObject,
    mut v___y_8924_: *mut crate::leanh::LeanObject,
    mut v___y_8925_: *mut crate::leanh::LeanObject,
    mut v___y_8926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_8927_: usize = 0;
    let mut v_i_boxed_8928_: usize = 0;
    let mut v_res_8929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_8927_ = crate::leanh::lean_unbox_usize(v_sz_8920_);
    crate::leanh::lean_dec(v_sz_8920_);
    v_i_boxed_8928_ = crate::leanh::lean_unbox_usize(v_i_8921_);
    crate::leanh::lean_dec(v_i_8921_);
    v_res_8929_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(v_pre_8918_, v_post_8919_, v_sz_boxed_8927_, v_i_boxed_8928_, v_bs_8922_, v___y_8923_, v___y_8924_, v___y_8925_);
    crate::leanh::lean_dec(v___y_8925_);
    crate::leanh::lean_dec_ref(v___y_8924_);
    crate::leanh::lean_dec(v___y_8923_);
    return v_res_8929_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___boxed(
    mut v_pre_8930_: *mut crate::leanh::LeanObject,
    mut v_post_8931_: *mut crate::leanh::LeanObject,
    mut v_x_8932_: *mut crate::leanh::LeanObject,
    mut v_x_8933_: *mut crate::leanh::LeanObject,
    mut v_x_8934_: *mut crate::leanh::LeanObject,
    mut v___y_8935_: *mut crate::leanh::LeanObject,
    mut v___y_8936_: *mut crate::leanh::LeanObject,
    mut v___y_8937_: *mut crate::leanh::LeanObject,
    mut v___y_8938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8939_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_8930_, v_post_8931_, v_x_8932_, v_x_8933_, v_x_8934_, v___y_8935_, v___y_8936_, v___y_8937_);
    crate::leanh::lean_dec(v___y_8937_);
    crate::leanh::lean_dec_ref(v___y_8936_);
    crate::leanh::lean_dec(v___y_8935_);
    return v_res_8939_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___boxed(
    mut v_pre_8940_: *mut crate::leanh::LeanObject,
    mut v_post_8941_: *mut crate::leanh::LeanObject,
    mut v_e_8942_: *mut crate::leanh::LeanObject,
    mut v_a_8943_: *mut crate::leanh::LeanObject,
    mut v___y_8944_: *mut crate::leanh::LeanObject,
    mut v___y_8945_: *mut crate::leanh::LeanObject,
    mut v___y_8946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8947_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_8940_, v_post_8941_, v_e_8942_, v_a_8943_, v___y_8944_, v___y_8945_);
    crate::leanh::lean_dec(v___y_8945_);
    crate::leanh::lean_dec_ref(v___y_8944_);
    crate::leanh::lean_dec(v_a_8943_);
    return v_res_8947_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(
    mut v_00_u03b1_8948_: *mut crate::leanh::LeanObject,
    mut v_x_8949_: *mut crate::leanh::LeanObject,
    mut v___y_8950_: *mut crate::leanh::LeanObject,
    mut v___y_8951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8953_ = crate::leanh::lean_apply_1(v_x_8949_, crate::leanh::lean_box(0));
    v___x_8954_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_8954_, 0, v___x_8953_);
    return v___x_8954_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0___boxed(
    mut v_00_u03b1_8955_: *mut crate::leanh::LeanObject,
    mut v_x_8956_: *mut crate::leanh::LeanObject,
    mut v___y_8957_: *mut crate::leanh::LeanObject,
    mut v___y_8958_: *mut crate::leanh::LeanObject,
    mut v___y_8959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8960_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(
        v_00_u03b1_8955_,
        v_x_8956_,
        v___y_8957_,
        v___y_8958_,
    );
    crate::leanh::lean_dec(v___y_8958_);
    crate::leanh::lean_dec_ref(v___y_8957_);
    return v_res_8960_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(
    mut v_input_8961_: *mut crate::leanh::LeanObject,
    mut v_pre_8962_: *mut crate::leanh::LeanObject,
    mut v_post_8963_: *mut crate::leanh::LeanObject,
    mut v___y_8964_: *mut crate::leanh::LeanObject,
    mut v___y_8965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8976_: u8 = 0;
    let mut v___x_8978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8980_: u8 = 0;
    let mut v_unused_8981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8967_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once), _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
                v___x_8968_ =
                    l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(
                        crate::leanh::lean_box(0),
                        v___x_8967_,
                        v___y_8964_,
                        v___y_8965_,
                    );
                v_a_8969_ = crate::leanh::lean_ctor_get(v___x_8968_, 0);
                crate::leanh::lean_inc(v_a_8969_);
                crate::leanh::lean_dec_ref(v___x_8968_);
                v___x_8970_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_8962_, v_post_8963_, v_input_8961_, v_a_8969_, v___y_8964_, v___y_8965_);
                if crate::leanh::lean_obj_tag(v___x_8970_) == 0 {
                    v_a_8971_ = crate::leanh::lean_ctor_get(v___x_8970_, 0);
                    crate::leanh::lean_inc(v_a_8971_);
                    crate::leanh::lean_dec_ref_known(v___x_8970_, 1);
                    v___x_8972_ = crate::leanh::lean_alloc_closure(
                        l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___x_8972_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_8972_, 1, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_8972_, 2, v_a_8969_);
                    v___x_8973_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(crate::leanh::lean_box(0), v___x_8972_, v___y_8964_, v___y_8965_);
                    v_isSharedCheck_8980_ = (!crate::leanh::lean_is_exclusive(v___x_8973_)) as u8;
                    if v_isSharedCheck_8980_ == 0 {
                        v_unused_8981_ = crate::leanh::lean_ctor_get(v___x_8973_, 0);
                        crate::leanh::lean_dec(v_unused_8981_);
                        v___x_8975_ = v___x_8973_;
                        v_isShared_8976_ = v_isSharedCheck_8980_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_8973_);
                        v___x_8975_ = crate::leanh::lean_box(0);
                        v_isShared_8976_ = v_isSharedCheck_8980_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_8969_);
                    return v___x_8970_;
                }
            }
            1 => {
                if v_isShared_8976_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8975_, 0, v_a_8971_);
                    v___x_8978_ = v___x_8975_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8979_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8979_, 0, v_a_8971_);
                    v___x_8978_ = v_reuseFailAlloc_8979_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8978_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___boxed(
    mut v_input_8982_: *mut crate::leanh::LeanObject,
    mut v_pre_8983_: *mut crate::leanh::LeanObject,
    mut v_post_8984_: *mut crate::leanh::LeanObject,
    mut v___y_8985_: *mut crate::leanh::LeanObject,
    mut v___y_8986_: *mut crate::leanh::LeanObject,
    mut v___y_8987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8988_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(
        v_input_8982_,
        v_pre_8983_,
        v_post_8984_,
        v___y_8985_,
        v___y_8986_,
    );
    crate::leanh::lean_dec(v___y_8986_);
    crate::leanh::lean_dec_ref(v___y_8985_);
    return v_res_8988_;
}
pub unsafe fn l_Lean_Meta_Sym_normalizeLevels(
    mut v_e_8991_: *mut crate::leanh::LeanObject,
    mut v_a_8992_: *mut crate::leanh::LeanObject,
    mut v_a_8993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8995_: u8 = 0;
    v___x_8995_ =
        l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(v_e_8991_);
    if v___x_8995_ == 0 {
        let mut v_pre_8996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_8997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_8996_ = l_Lean_Meta_Sym_normalizeLevels___closed__0;
        v___f_8997_ = l_Lean_Meta_Sym_normalizeLevels___closed__1;
        v___x_8998_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(
            v_e_8991_,
            v_pre_8996_,
            v___f_8997_,
            v_a_8992_,
            v_a_8993_,
        );
        return v___x_8998_;
    } else {
        let mut v___x_8999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_8999_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_8999_, 0, v_e_8991_);
        return v___x_8999_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_normalizeLevels___boxed(
    mut v_e_9000_: *mut crate::leanh::LeanObject,
    mut v_a_9001_: *mut crate::leanh::LeanObject,
    mut v_a_9002_: *mut crate::leanh::LeanObject,
    mut v_a_9003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_9004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_9004_ = l_Lean_Meta_Sym_normalizeLevels(v_e_9000_, v_a_9001_, v_a_9002_);
    crate::leanh::lean_dec(v_a_9002_);
    crate::leanh::lean_dec_ref(v_a_9001_);
    return v_res_9004_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6(
    mut v_00_u03b1_9005_: *mut crate::leanh::LeanObject,
    mut v_ref_9006_: *mut crate::leanh::LeanObject,
    mut v___y_9007_: *mut crate::leanh::LeanObject,
    mut v___y_9008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9010_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg(v_ref_9006_);
    return v___x_9010_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___boxed(
    mut v_00_u03b1_9011_: *mut crate::leanh::LeanObject,
    mut v_ref_9012_: *mut crate::leanh::LeanObject,
    mut v___y_9013_: *mut crate::leanh::LeanObject,
    mut v___y_9014_: *mut crate::leanh::LeanObject,
    mut v___y_9015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_9016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_9016_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6(v_00_u03b1_9011_, v_ref_9012_, v___y_9013_, v___y_9014_);
    crate::leanh::lean_dec(v___y_9014_);
    crate::leanh::lean_dec_ref(v___y_9013_);
    return v_res_9016_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7(
    mut v_00_u03b1_9017_: *mut crate::leanh::LeanObject,
    mut v___y_9018_: *mut crate::leanh::LeanObject,
    mut v___y_9019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9021_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg();
    return v___x_9021_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___boxed(
    mut v_00_u03b1_9022_: *mut crate::leanh::LeanObject,
    mut v___y_9023_: *mut crate::leanh::LeanObject,
    mut v___y_9024_: *mut crate::leanh::LeanObject,
    mut v___y_9025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_9026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_9026_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7(v_00_u03b1_9022_, v___y_9023_, v___y_9024_);
    crate::leanh::lean_dec(v___y_9024_);
    crate::leanh::lean_dec_ref(v___y_9023_);
    return v_res_9026_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(
    mut v_00_u03b1_9027_: *mut crate::leanh::LeanObject,
    mut v_x_9028_: *mut crate::leanh::LeanObject,
    mut v___y_9029_: *mut crate::leanh::LeanObject,
    mut v___y_9030_: *mut crate::leanh::LeanObject,
    mut v___y_9031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9033_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg(v_x_9028_, v___y_9029_, v___y_9030_, v___y_9031_);
    return v___x_9033_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___boxed(
    mut v_00_u03b1_9034_: *mut crate::leanh::LeanObject,
    mut v_x_9035_: *mut crate::leanh::LeanObject,
    mut v___y_9036_: *mut crate::leanh::LeanObject,
    mut v___y_9037_: *mut crate::leanh::LeanObject,
    mut v___y_9038_: *mut crate::leanh::LeanObject,
    mut v___y_9039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_9040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_9040_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(v_00_u03b1_9034_, v_x_9035_, v___y_9036_, v___y_9037_, v___y_9038_);
    crate::leanh::lean_dec(v___y_9038_);
    crate::leanh::lean_dec_ref(v___y_9037_);
    crate::leanh::lean_dec(v___y_9036_);
    return v_res_9040_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Util(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Transform(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_WHNF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ForEachExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Util(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Util(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_SymM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Transform(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_WHNF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_ForEachExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Util(builtin);
}

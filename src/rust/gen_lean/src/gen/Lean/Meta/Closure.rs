// Lean compiler output
// Module: Lean.Meta.Closure
// Imports: Lean.Meta.Check Lean.Meta.Tactic.AuxLemma Lean.Util.ForEachExpr
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_size, lean_array_pop, lean_array_push, lean_array_size, lean_array_to_list,
    lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_expr_abstract,
    lean_expr_abstract_range, lean_expr_eqv, lean_expr_has_loose_bvar, lean_expr_lower_loose_bvars,
    lean_infer_type, lean_level_eq, lean_mk_array, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_panic_fn_borrowed, lean_ptr_addr, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_uint32_add, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land,
    lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::State::{
    l_StateT_bind, l_StateT_instMonad___redArg___lam__1, l_StateT_instMonad___redArg___lam__4,
    l_StateT_instMonad___redArg___lam__7, l_StateT_instMonad___redArg___lam__9, l_StateT_map,
    l_StateT_pure,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map, l_Array_reverse___redArg,
};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Nat::Fold::l_Nat_foldRev___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Meta::Defs::lean_name_append_index_after;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_num___override,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::{l_mkPanicMessageWithDecl, l_ptrEqList___redArg};
use crate::r#gen::Lean::AddDecl::l_Lean_addDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instInhabitedCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__0___boxed,
    l_Lean_Core_instMonadCoreM___lam__1___boxed, l_Lean_compileDecl,
};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Environment::{l_Lean_Environment_hasUnsafe, l_Lean_getMaxHeight};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_const___override, l_Lean_Expr_forallE___override,
    l_Lean_Expr_fvarId_x21, l_Lean_Expr_hasFVar, l_Lean_Expr_hasLevelParam, l_Lean_Expr_hasMVar,
    l_Lean_Expr_hash, l_Lean_Expr_headBeta, l_Lean_Expr_isFVar, l_Lean_Expr_lam___override,
    l_Lean_Expr_letE___override, l_Lean_Expr_mdata___override, l_Lean_Expr_proj___override,
    l_Lean_Expr_sort___override, l_Lean_ExprStructEq_beq, l_Lean_ExprStructEq_beq___boxed,
    l_Lean_ExprStructEq_hash, l_Lean_ExprStructEq_hash___boxed, l_Lean_instBEqBinderInfo_beq,
    l_Lean_instBEqFVarId_beq, l_Lean_instEmptyCollectionFVarIdHashSet,
    l_Lean_instHashableFVarId_hash, l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkFVar, l_Lean_mkForall,
    l_Lean_mkLambda,
};
use crate::r#gen::Lean::Level::{
    l_Lean_Level_beq___boxed, l_Lean_Level_hasMVar, l_Lean_Level_hasParam, l_Lean_Level_hash,
    l_Lean_Level_hash___boxed, l_Lean_Level_succ___override, l_Lean_mkLevelIMax_x27,
    l_Lean_mkLevelMax_x27, l_Lean_mkLevelParam, l_Lean_simpLevelIMax_x27, l_Lean_simpLevelMax_x27,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_get_x21, l_Lean_LocalDecl_fvarId, l_Lean_LocalDecl_index,
    l_Lean_LocalDecl_isLet, l_Lean_LocalDecl_replaceFVarId, l_Lean_LocalDecl_toExpr,
    l_Lean_LocalDecl_type,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofList, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux,
    l_Lean_FVarId_getDecl___redArg, l_Lean_FVarId_getValue_x3f___redArg, l_Lean_MVarId_getDecl,
    l_Lean_Meta_getZetaDeltaFVarIds___redArg, l_Lean_Meta_instInhabitedMetaM___lam__0___boxed,
    l_Lean_Meta_mkLambdaFVars,
};
use crate::r#gen::Lean::Meta::Check::{
    initialize_Lean_Meta_Check, l_Lean_Meta_check, runtime_initialize_Lean_Meta_Check,
};
use crate::r#gen::Lean::Meta::Tactic::AuxLemma::{
    initialize_Lean_Meta_Tactic_AuxLemma, l_Lean_Meta_mkAuxLemma,
    runtime_initialize_Lean_Meta_Tactic_AuxLemma,
};
use crate::r#gen::Lean::MetavarContext::{
    l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f, l_Lean_instantiateMVarsCore,
};
use crate::r#gen::Lean::Util::ForEachExpr::{
    initialize_Lean_Util_ForEachExpr, runtime_initialize_Lean_Util_ForEachExpr,
};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insert___redArg,
};
pub static l_Lean_Meta_Closure_instInhabitedToProcessElement_default___closed__0_value:
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
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Closure_instInhabitedToProcessElement_default___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Closure_instInhabitedToProcessElement_default___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Closure_instInhabitedToProcessElement_default:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Closure_instInhabitedToProcessElement_default___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Closure_instInhabitedToProcessElement: *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Closure_instInhabitedToProcessElement_default___closed__0_value
)
    as *mut leanh::LeanObject;
pub static l_Lean_Meta_Closure_visitLevel___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Level_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Closure_visitLevel___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Closure_visitLevel___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Closure_visitLevel___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Level_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Closure_visitLevel___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Closure_visitLevel___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Closure_visitExpr___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_ExprStructEq_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Closure_visitExpr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Closure_visitExpr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Closure_visitExpr___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_ExprStructEq_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Closure_visitExpr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Closure_visitExpr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__0_value:
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
    m_data: [117, 0],
};
static mut l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        12562556307207860968 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Closure_mkNextUserName___redArg___closed__0_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [95, 120, 0],
};
static mut l_Lean_Meta_Closure_mkNextUserName___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Closure_mkNextUserName___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Closure_mkNextUserName___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Closure_mkNextUserName___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        7699194985028780469 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Closure_mkNextUserName___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Closure_mkNextUserName___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Closure_mkBinding___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_LocalDecl_toExpr as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Closure_mkBinding___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Closure_mkBinding___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Closure_mkBinding___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Closure_mkBinding___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Closure_mkBinding___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Closure_mkBinding___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Closure_mkBinding___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Closure_mkBinding___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Closure_mkBinding___closed__3_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Closure_mkBinding___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Closure_mkBinding___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Closure_mkBinding___closed__4_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Closure_mkBinding___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Closure_mkBinding___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Closure_mkBinding___closed__5_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Closure_mkBinding___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Closure_mkBinding___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Closure_mkBinding___closed__6_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Closure_mkBinding___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Closure_mkBinding___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Closure_mkBinding___closed__7_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Closure_mkBinding___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Closure_mkBinding___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Closure_mkBinding___closed__8_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Meta_Closure_mkBinding___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Closure_mkBinding___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Closure_mkBinding___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Closure_mkBinding___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Closure_mkBinding___closed__9_value: leanh::LeanCtorObject<5> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Closure_mkBinding___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Closure_mkBinding___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Closure_mkBinding___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Closure_mkBinding___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Closure_mkBinding___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Closure_mkBinding___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Closure_mkBinding___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Closure_mkBinding___closed__10_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Meta_Closure_mkBinding___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Closure_mkBinding___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Closure_mkBinding___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Closure_mkBinding___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__1_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__4_value:
    leanh::LeanStringObject<84> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 84,
    m_capacity: 84,
    m_length: 83,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 33, 100, 101, 99, 108, 46, 105, 115, 76, 101, 116, 32, 40, 97, 108, 108, 111, 119,
        78, 111, 110, 100, 101, 112, 32, 58, 61, 32, 116, 114, 117, 101, 41, 32, 45, 45, 32, 115,
        104, 111, 117, 108, 100, 32, 97, 108, 108, 32, 98, 101, 32, 99, 100, 101, 99, 108, 115, 10,
        32, 32, 32, 32, 0,
    ],
};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__4_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3_value:
    leanh::LeanStringObject<63> = leanh::LeanStringObject {
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
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67,
        108, 111, 115, 117, 114, 101, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67,
        108, 111, 115, 117, 114, 101, 46, 115, 111, 114, 116, 68, 101, 99, 108, 115, 46, 118, 105,
        115, 105, 116, 0,
    ],
};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2_value:
    leanh::LeanStringObject<18> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67, 108, 111, 115, 117, 114, 101, 0,
    ],
};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__6_value:
    leanh::LeanStringObject<47> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 47,
    m_capacity: 47,
    m_length: 46,
    m_data: [
        99, 121, 99, 108, 101, 32, 100, 101, 116, 101, 99, 116, 101, 100, 32, 105, 110, 32, 115,
        111, 114, 116, 105, 110, 103, 32, 97, 98, 115, 116, 114, 97, 99, 116, 101, 100, 32, 118,
        97, 114, 105, 97, 98, 108, 101, 115, 0,
    ],
};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__6_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__9_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [67, 108, 111, 115, 117, 114, 101, 0],
};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__9_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__8_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [77, 101, 116, 97, 0],
};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__8_value
) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__8_value) as *mut leanh::LeanObject,142734480563613395 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__9_value) as *mut leanh::LeanObject,1977693072266780920 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__11_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__11_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__12_value:
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
            l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__11_value
        ) as *mut leanh::LeanObject,
        14231257465488249300 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__12:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__12_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14_value:
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
    m_data: [
        83, 111, 114, 116, 105, 110, 103, 32, 100, 101, 99, 108, 32, 0,
    ],
};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__16_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [32, 58, 32, 0],
};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__16:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__16_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instInhabitedCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0_value:
    leanh::LeanStringObject<57> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 57,
    m_capacity: 57,
    m_length: 56,
    m_data: [
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67,
        108, 111, 115, 117, 114, 101, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67,
        108, 111, 115, 117, 114, 101, 46, 115, 111, 114, 116, 68, 101, 99, 108, 115, 0,
    ],
};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__1_value:
    leanh::LeanStringObject<59> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 59,
    m_capacity: 59,
    m_length: 58,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 115, 111, 114, 116, 101, 100, 68, 101, 99, 108, 115, 46, 115, 105, 122, 101, 32,
        61, 32, 115, 111, 114, 116, 101, 100, 65, 114, 103, 115, 46, 115, 105, 122, 101, 10, 32,
        32, 0,
    ],
};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__1_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__3_value:
    leanh::LeanStringObject<59> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 59,
    m_capacity: 59,
    m_length: 58,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 116, 111, 83, 111, 114, 116, 68, 101, 99, 108, 115, 46, 115, 105, 122, 101, 32, 61,
        32, 116, 111, 83, 111, 114, 116, 65, 114, 103, 115, 46, 115, 105, 122, 101, 10, 32, 32, 0,
    ],
};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__3_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__7_value:
    leanh::LeanStringObject<15> = leanh::LeanStringObject {
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
        83, 111, 114, 116, 101, 100, 32, 102, 118, 97, 114, 115, 58, 32, 0,
    ],
};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__7_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__9_value:
    leanh::LeanStringObject<66> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 66,
    m_capacity: 66,
    m_length: 65,
    m_data: [
        77, 86, 97, 114, 115, 32, 116, 111, 32, 97, 98, 115, 116, 114, 97, 99, 116, 44, 32, 116,
        111, 112, 111, 108, 111, 103, 105, 99, 97, 108, 108, 121, 32, 115, 111, 114, 116, 105, 110,
        103, 32, 116, 104, 101, 32, 97, 98, 115, 116, 114, 97, 99, 116, 101, 100, 32, 118, 97, 114,
        105, 97, 98, 108, 101, 115, 0,
    ],
};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__9_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___closed__0_value:
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
static mut l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Closure_mkValueTypeClosure___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Closure_mkValueTypeClosure___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Closure_mkValueTypeClosure___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Closure_mkValueTypeClosure___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Closure_mkValueTypeClosure___closed__2_value: leanh::LeanArrayObject<
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
static mut l_Lean_Meta_Closure_mkValueTypeClosure___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Closure_mkValueTypeClosure___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Closure_mkValueTypeClosure___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Closure_mkValueTypeClosure___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Closure_mkValueTypeClosure___closed__4_value:
    leanh::LeanStringObject<37> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67, 108, 111, 115, 117, 114, 101, 46, 109, 107,
        86, 97, 108, 117, 101, 84, 121, 112, 101, 67, 108, 111, 115, 117, 114, 101, 0,
    ],
};
static mut l_Lean_Meta_Closure_mkValueTypeClosure___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Closure_mkValueTypeClosure___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Closure_mkValueTypeClosure___closed__5_value:
    leanh::LeanStringObject<124> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 124,
    m_capacity: 124,
    m_length: 123,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 33, 118, 97, 108, 117, 101, 46, 104, 97, 115, 70, 86, 97, 114, 32, 32, 45, 45, 32,
        73, 110, 32, 99, 97, 115, 101, 32, 104, 116, 116, 112, 115, 58, 47, 47, 103, 105, 116, 104,
        117, 98, 46, 99, 111, 109, 47, 108, 101, 97, 110, 112, 114, 111, 118, 101, 114, 47, 108,
        101, 97, 110, 52, 47, 105, 115, 115, 117, 101, 115, 47, 49, 48, 55, 48, 53, 32, 114, 101,
        115, 117, 114, 102, 97, 99, 101, 115, 32, 105, 110, 32, 97, 32, 110, 101, 119, 32, 119, 97,
        121, 10, 32, 32, 0,
    ],
};
static mut l_Lean_Meta_Closure_mkValueTypeClosure___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Closure_mkValueTypeClosure___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Closure_mkValueTypeClosure___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Closure_mkValueTypeClosure___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__8_value) as *mut leanh::LeanObject,13556645696814629918 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__9_value) as *mut leanh::LeanObject,6031022709731647993 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,1473213575506997980 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12206470351704719357 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__8_value) as *mut leanh::LeanObject,17035210283142786325 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2743663518592930620 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10396343488372244021 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13224073964607178912 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__8_value) as *mut leanh::LeanObject,9725506522067437068 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__9_value) as *mut leanh::LeanObject,954710903781754323 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 210311863 as usize) << 1) | 1) as *mut leanh::LeanObject,3484035832308642304 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3427702989600336855 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5720014134600825151 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,12352986725679511930 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Closure_visitLevel(
    mut v_f_4526_: *mut leanh::LeanObject,
    mut v_u_4527_: *mut leanh::LeanObject,
    mut v_a_4528_: u8,
    mut v_a_4529_: *mut leanh::LeanObject,
    mut v_a_4530_: *mut leanh::LeanObject,
    mut v_a_4531_: *mut leanh::LeanObject,
    mut v_a_4532_: *mut leanh::LeanObject,
    mut v_a_4533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4546_: u8 = 0;
    let mut v___x_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextLevelIdx_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelArgs_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDecls_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDeclsForMVars_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLetDecls_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextExprIdx_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprMVarArgs_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprFVarArgs_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toProcess_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4562_: u8 = 0;
    let mut v___x_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4571_: u8 = 0;
    let mut v_isSharedCheck_4572_: u8 = 0;
    let mut v_val_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4576_: u8 = 0;
    let mut v___x_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4580_: u8 = 0;
    let mut v___x_4581_: u8 = 0;
    let mut v___x_4582_: u8 = 0;
    let mut v___x_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4581_ = l_Lean_Level_hasMVar(v_u_4527_);
                if v___x_4581_ == 0 {
                    v___x_4582_ = l_Lean_Level_hasParam(v_u_4527_);
                    if v___x_4582_ == 0 {
                        leanh::lean_dec_ref(v_f_4526_);
                        v___x_4583_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4583_, 0, v_u_4527_);
                        return v___x_4583_;
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
                v___x_4536_ = lean_st_ref_get(v_a_4529_);
                v_visitedLevel_4537_ = leanh::lean_ctor_get(v___x_4536_, 0);
                leanh::lean_inc_ref(v_visitedLevel_4537_);
                leanh::lean_dec(v___x_4536_);
                v___x_4538_ = l_Lean_Meta_Closure_visitLevel___closed__0;
                v___x_4539_ = l_Lean_Meta_Closure_visitLevel___closed__1;
                leanh::lean_inc(v_u_4527_);
                v___x_4540_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
                    v___x_4538_,
                    v___x_4539_,
                    v_visitedLevel_4537_,
                    v_u_4527_,
                );
                leanh::lean_dec_ref(v_visitedLevel_4537_);
                if leanh::lean_obj_tag(v___x_4540_) == 0 {
                    v___x_4541_ = leanh::lean_box((v_a_4528_) as usize);
                    leanh::lean_inc(v_a_4533_);
                    leanh::lean_inc_ref(v_a_4532_);
                    leanh::lean_inc(v_a_4531_);
                    leanh::lean_inc_ref(v_a_4530_);
                    leanh::lean_inc(v_a_4529_);
                    leanh::lean_inc(v_u_4527_);
                    v___x_4542_ = leanh::lean_apply_8(
                        v_f_4526_,
                        v_u_4527_,
                        v___x_4541_,
                        v_a_4529_,
                        v_a_4530_,
                        v_a_4531_,
                        v_a_4532_,
                        v_a_4533_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_4542_) == 0 {
                        v_a_4543_ = leanh::lean_ctor_get(v___x_4542_, 0);
                        v_isSharedCheck_4572_ =
                            (!leanh::lean_is_exclusive(v___x_4542_)) as u8;
                        if v_isSharedCheck_4572_ == 0 {
                            v___x_4545_ = v___x_4542_;
                            v_isShared_4546_ = v_isSharedCheck_4572_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4543_);
                            leanh::lean_dec(v___x_4542_);
                            v___x_4545_ = leanh::lean_box(0);
                            v_isShared_4546_ = v_isSharedCheck_4572_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_u_4527_);
                        return v___x_4542_;
                    }
                } else {
                    leanh::lean_dec(v_u_4527_);
                    leanh::lean_dec_ref(v_f_4526_);
                    v_val_4573_ = leanh::lean_ctor_get(v___x_4540_, 0);
                    v_isSharedCheck_4580_ = (!leanh::lean_is_exclusive(v___x_4540_)) as u8;
                    if v_isSharedCheck_4580_ == 0 {
                        v___x_4575_ = v___x_4540_;
                        v_isShared_4576_ = v_isSharedCheck_4580_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4573_);
                        leanh::lean_dec(v___x_4540_);
                        v___x_4575_ = leanh::lean_box(0);
                        v_isShared_4576_ = v_isSharedCheck_4580_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4547_ = lean_st_ref_take(v_a_4529_);
                v_visitedLevel_4548_ = leanh::lean_ctor_get(v___x_4547_, 0);
                v_visitedExpr_4549_ = leanh::lean_ctor_get(v___x_4547_, 1);
                v_levelParams_4550_ = leanh::lean_ctor_get(v___x_4547_, 2);
                v_nextLevelIdx_4551_ = leanh::lean_ctor_get(v___x_4547_, 3);
                v_levelArgs_4552_ = leanh::lean_ctor_get(v___x_4547_, 4);
                v_newLocalDecls_4553_ = leanh::lean_ctor_get(v___x_4547_, 5);
                v_newLocalDeclsForMVars_4554_ = leanh::lean_ctor_get(v___x_4547_, 6);
                v_newLetDecls_4555_ = leanh::lean_ctor_get(v___x_4547_, 7);
                v_nextExprIdx_4556_ = leanh::lean_ctor_get(v___x_4547_, 8);
                v_exprMVarArgs_4557_ = leanh::lean_ctor_get(v___x_4547_, 9);
                v_exprFVarArgs_4558_ = leanh::lean_ctor_get(v___x_4547_, 10);
                v_toProcess_4559_ = leanh::lean_ctor_get(v___x_4547_, 11);
                v_isSharedCheck_4571_ = (!leanh::lean_is_exclusive(v___x_4547_)) as u8;
                if v_isSharedCheck_4571_ == 0 {
                    v___x_4561_ = v___x_4547_;
                    v_isShared_4562_ = v_isSharedCheck_4571_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_toProcess_4559_);
                    leanh::lean_inc(v_exprFVarArgs_4558_);
                    leanh::lean_inc(v_exprMVarArgs_4557_);
                    leanh::lean_inc(v_nextExprIdx_4556_);
                    leanh::lean_inc(v_newLetDecls_4555_);
                    leanh::lean_inc(v_newLocalDeclsForMVars_4554_);
                    leanh::lean_inc(v_newLocalDecls_4553_);
                    leanh::lean_inc(v_levelArgs_4552_);
                    leanh::lean_inc(v_nextLevelIdx_4551_);
                    leanh::lean_inc(v_levelParams_4550_);
                    leanh::lean_inc(v_visitedExpr_4549_);
                    leanh::lean_inc(v_visitedLevel_4548_);
                    leanh::lean_dec(v___x_4547_);
                    v___x_4561_ = leanh::lean_box(0);
                    v_isShared_4562_ = v_isSharedCheck_4571_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc(v_a_4543_);
                v___x_4563_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                    v___x_4538_,
                    v___x_4539_,
                    v_visitedLevel_4548_,
                    v_u_4527_,
                    v_a_4543_,
                );
                if v_isShared_4562_ == 0 {
                    leanh::lean_ctor_set(v___x_4561_, 0, v___x_4563_);
                    v___x_4565_ = v___x_4561_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4570_ = leanh::lean_alloc_ctor(0, 12, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 0, v___x_4563_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 1, v_visitedExpr_4549_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 2, v_levelParams_4550_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 3, v_nextLevelIdx_4551_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 4, v_levelArgs_4552_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 5, v_newLocalDecls_4553_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4570_,
                        6,
                        v_newLocalDeclsForMVars_4554_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 7, v_newLetDecls_4555_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 8, v_nextExprIdx_4556_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 9, v_exprMVarArgs_4557_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 10, v_exprFVarArgs_4558_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 11, v_toProcess_4559_);
                    v___x_4565_ = v_reuseFailAlloc_4570_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4566_ = lean_st_ref_set(v_a_4529_, v___x_4565_);
                if v_isShared_4546_ == 0 {
                    v___x_4568_ = v___x_4545_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4569_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_a_4543_);
                    v___x_4568_ = v_reuseFailAlloc_4569_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4568_;
            }
            6 => {
                if v_isShared_4576_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4575_, 0);
                    v___x_4578_ = v___x_4575_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4579_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4579_, 0, v_val_4573_);
                    v___x_4578_ = v_reuseFailAlloc_4579_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4578_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Closure_visitLevel___boxed(
    mut v_f_4584_: *mut leanh::LeanObject,
    mut v_u_4585_: *mut leanh::LeanObject,
    mut v_a_4586_: *mut leanh::LeanObject,
    mut v_a_4587_: *mut leanh::LeanObject,
    mut v_a_4588_: *mut leanh::LeanObject,
    mut v_a_4589_: *mut leanh::LeanObject,
    mut v_a_4590_: *mut leanh::LeanObject,
    mut v_a_4591_: *mut leanh::LeanObject,
    mut v_a_4592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_4593_: u8 = 0;
    let mut v_res_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_4593_ = (leanh::lean_unbox(v_a_4586_) as u8);
    v_res_4594_ = l_Lean_Meta_Closure_visitLevel(
        v_f_4584_,
        v_u_4585_,
        v_a_boxed_4593_,
        v_a_4587_,
        v_a_4588_,
        v_a_4589_,
        v_a_4590_,
        v_a_4591_,
    );
    leanh::lean_dec(v_a_4591_);
    leanh::lean_dec_ref(v_a_4590_);
    leanh::lean_dec(v_a_4589_);
    leanh::lean_dec_ref(v_a_4588_);
    leanh::lean_dec(v_a_4587_);
    return v_res_4594_;
}
pub unsafe fn l_Lean_Meta_Closure_visitExpr(
    mut v_f_4597_: *mut leanh::LeanObject,
    mut v_e_4598_: *mut leanh::LeanObject,
    mut v_a_4599_: u8,
    mut v_a_4600_: *mut leanh::LeanObject,
    mut v_a_4601_: *mut leanh::LeanObject,
    mut v_a_4602_: *mut leanh::LeanObject,
    mut v_a_4603_: *mut leanh::LeanObject,
    mut v_a_4604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4617_: u8 = 0;
    let mut v___x_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextLevelIdx_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelArgs_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDecls_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDeclsForMVars_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLetDecls_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextExprIdx_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprMVarArgs_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprFVarArgs_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toProcess_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4633_: u8 = 0;
    let mut v___x_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4642_: u8 = 0;
    let mut v_isSharedCheck_4643_: u8 = 0;
    let mut v_val_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4647_: u8 = 0;
    let mut v___x_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4651_: u8 = 0;
    let mut v___x_4652_: u8 = 0;
    let mut v___x_4653_: u8 = 0;
    let mut v___x_4654_: u8 = 0;
    let mut v___x_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4652_ = l_Lean_Expr_hasLevelParam(v_e_4598_);
                if v___x_4652_ == 0 {
                    v___x_4653_ = l_Lean_Expr_hasFVar(v_e_4598_);
                    if v___x_4653_ == 0 {
                        v___x_4654_ = l_Lean_Expr_hasMVar(v_e_4598_);
                        if v___x_4654_ == 0 {
                            leanh::lean_dec_ref(v_f_4597_);
                            v___x_4655_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_4655_, 0, v_e_4598_);
                            return v___x_4655_;
                        } else {
                            state = 1;
                            continue;
                        }
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
                v___x_4607_ = lean_st_ref_get(v_a_4600_);
                v_visitedExpr_4608_ = leanh::lean_ctor_get(v___x_4607_, 1);
                leanh::lean_inc_ref(v_visitedExpr_4608_);
                leanh::lean_dec(v___x_4607_);
                v___x_4609_ = l_Lean_Meta_Closure_visitExpr___closed__0;
                v___x_4610_ = l_Lean_Meta_Closure_visitExpr___closed__1;
                leanh::lean_inc_ref(v_e_4598_);
                v___x_4611_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
                    v___x_4609_,
                    v___x_4610_,
                    v_visitedExpr_4608_,
                    v_e_4598_,
                );
                leanh::lean_dec_ref(v_visitedExpr_4608_);
                if leanh::lean_obj_tag(v___x_4611_) == 0 {
                    v___x_4612_ = leanh::lean_box((v_a_4599_) as usize);
                    leanh::lean_inc(v_a_4604_);
                    leanh::lean_inc_ref(v_a_4603_);
                    leanh::lean_inc(v_a_4602_);
                    leanh::lean_inc_ref(v_a_4601_);
                    leanh::lean_inc(v_a_4600_);
                    leanh::lean_inc_ref(v_e_4598_);
                    v___x_4613_ = leanh::lean_apply_8(
                        v_f_4597_,
                        v_e_4598_,
                        v___x_4612_,
                        v_a_4600_,
                        v_a_4601_,
                        v_a_4602_,
                        v_a_4603_,
                        v_a_4604_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_4613_) == 0 {
                        v_a_4614_ = leanh::lean_ctor_get(v___x_4613_, 0);
                        v_isSharedCheck_4643_ =
                            (!leanh::lean_is_exclusive(v___x_4613_)) as u8;
                        if v_isSharedCheck_4643_ == 0 {
                            v___x_4616_ = v___x_4613_;
                            v_isShared_4617_ = v_isSharedCheck_4643_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4614_);
                            leanh::lean_dec(v___x_4613_);
                            v___x_4616_ = leanh::lean_box(0);
                            v_isShared_4617_ = v_isSharedCheck_4643_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_4598_);
                        return v___x_4613_;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_4598_);
                    leanh::lean_dec_ref(v_f_4597_);
                    v_val_4644_ = leanh::lean_ctor_get(v___x_4611_, 0);
                    v_isSharedCheck_4651_ = (!leanh::lean_is_exclusive(v___x_4611_)) as u8;
                    if v_isSharedCheck_4651_ == 0 {
                        v___x_4646_ = v___x_4611_;
                        v_isShared_4647_ = v_isSharedCheck_4651_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4644_);
                        leanh::lean_dec(v___x_4611_);
                        v___x_4646_ = leanh::lean_box(0);
                        v_isShared_4647_ = v_isSharedCheck_4651_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4618_ = lean_st_ref_take(v_a_4600_);
                v_visitedLevel_4619_ = leanh::lean_ctor_get(v___x_4618_, 0);
                v_visitedExpr_4620_ = leanh::lean_ctor_get(v___x_4618_, 1);
                v_levelParams_4621_ = leanh::lean_ctor_get(v___x_4618_, 2);
                v_nextLevelIdx_4622_ = leanh::lean_ctor_get(v___x_4618_, 3);
                v_levelArgs_4623_ = leanh::lean_ctor_get(v___x_4618_, 4);
                v_newLocalDecls_4624_ = leanh::lean_ctor_get(v___x_4618_, 5);
                v_newLocalDeclsForMVars_4625_ = leanh::lean_ctor_get(v___x_4618_, 6);
                v_newLetDecls_4626_ = leanh::lean_ctor_get(v___x_4618_, 7);
                v_nextExprIdx_4627_ = leanh::lean_ctor_get(v___x_4618_, 8);
                v_exprMVarArgs_4628_ = leanh::lean_ctor_get(v___x_4618_, 9);
                v_exprFVarArgs_4629_ = leanh::lean_ctor_get(v___x_4618_, 10);
                v_toProcess_4630_ = leanh::lean_ctor_get(v___x_4618_, 11);
                v_isSharedCheck_4642_ = (!leanh::lean_is_exclusive(v___x_4618_)) as u8;
                if v_isSharedCheck_4642_ == 0 {
                    v___x_4632_ = v___x_4618_;
                    v_isShared_4633_ = v_isSharedCheck_4642_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_toProcess_4630_);
                    leanh::lean_inc(v_exprFVarArgs_4629_);
                    leanh::lean_inc(v_exprMVarArgs_4628_);
                    leanh::lean_inc(v_nextExprIdx_4627_);
                    leanh::lean_inc(v_newLetDecls_4626_);
                    leanh::lean_inc(v_newLocalDeclsForMVars_4625_);
                    leanh::lean_inc(v_newLocalDecls_4624_);
                    leanh::lean_inc(v_levelArgs_4623_);
                    leanh::lean_inc(v_nextLevelIdx_4622_);
                    leanh::lean_inc(v_levelParams_4621_);
                    leanh::lean_inc(v_visitedExpr_4620_);
                    leanh::lean_inc(v_visitedLevel_4619_);
                    leanh::lean_dec(v___x_4618_);
                    v___x_4632_ = leanh::lean_box(0);
                    v_isShared_4633_ = v_isSharedCheck_4642_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc(v_a_4614_);
                v___x_4634_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                    v___x_4609_,
                    v___x_4610_,
                    v_visitedExpr_4620_,
                    v_e_4598_,
                    v_a_4614_,
                );
                if v_isShared_4633_ == 0 {
                    leanh::lean_ctor_set(v___x_4632_, 1, v___x_4634_);
                    v___x_4636_ = v___x_4632_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4641_ = leanh::lean_alloc_ctor(0, 12, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4641_, 0, v_visitedLevel_4619_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4641_, 1, v___x_4634_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4641_, 2, v_levelParams_4621_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4641_, 3, v_nextLevelIdx_4622_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4641_, 4, v_levelArgs_4623_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4641_, 5, v_newLocalDecls_4624_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4641_,
                        6,
                        v_newLocalDeclsForMVars_4625_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4641_, 7, v_newLetDecls_4626_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4641_, 8, v_nextExprIdx_4627_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4641_, 9, v_exprMVarArgs_4628_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4641_, 10, v_exprFVarArgs_4629_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4641_, 11, v_toProcess_4630_);
                    v___x_4636_ = v_reuseFailAlloc_4641_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4637_ = lean_st_ref_set(v_a_4600_, v___x_4636_);
                if v_isShared_4617_ == 0 {
                    v___x_4639_ = v___x_4616_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4640_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4640_, 0, v_a_4614_);
                    v___x_4639_ = v_reuseFailAlloc_4640_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4639_;
            }
            6 => {
                if v_isShared_4647_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4646_, 0);
                    v___x_4649_ = v___x_4646_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4650_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4650_, 0, v_val_4644_);
                    v___x_4649_ = v_reuseFailAlloc_4650_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4649_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Closure_visitExpr___boxed(
    mut v_f_4656_: *mut leanh::LeanObject,
    mut v_e_4657_: *mut leanh::LeanObject,
    mut v_a_4658_: *mut leanh::LeanObject,
    mut v_a_4659_: *mut leanh::LeanObject,
    mut v_a_4660_: *mut leanh::LeanObject,
    mut v_a_4661_: *mut leanh::LeanObject,
    mut v_a_4662_: *mut leanh::LeanObject,
    mut v_a_4663_: *mut leanh::LeanObject,
    mut v_a_4664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_4665_: u8 = 0;
    let mut v_res_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_4665_ = (leanh::lean_unbox(v_a_4658_) as u8);
    v_res_4666_ = l_Lean_Meta_Closure_visitExpr(
        v_f_4656_,
        v_e_4657_,
        v_a_boxed_4665_,
        v_a_4659_,
        v_a_4660_,
        v_a_4661_,
        v_a_4662_,
        v_a_4663_,
    );
    leanh::lean_dec(v_a_4663_);
    leanh::lean_dec_ref(v_a_4662_);
    leanh::lean_dec(v_a_4661_);
    leanh::lean_dec_ref(v_a_4660_);
    leanh::lean_dec(v_a_4659_);
    return v_res_4666_;
}
pub unsafe fn l_Lean_Meta_Closure_mkNewLevelParam___redArg(
    mut v_u_4670_: *mut leanh::LeanObject,
    mut v_a_4671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextLevelIdx_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextLevelIdx_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelArgs_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDecls_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDeclsForMVars_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLetDecls_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextExprIdx_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprMVarArgs_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprFVarArgs_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toProcess_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4690_: u8 = 0;
    let mut v___x_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4703_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4673_ = lean_st_ref_get(v_a_4671_);
                v___x_4674_ = lean_st_ref_take(v_a_4671_);
                v_nextLevelIdx_4675_ = leanh::lean_ctor_get(v___x_4673_, 3);
                leanh::lean_inc(v_nextLevelIdx_4675_);
                leanh::lean_dec(v___x_4673_);
                v_visitedLevel_4676_ = leanh::lean_ctor_get(v___x_4674_, 0);
                v_visitedExpr_4677_ = leanh::lean_ctor_get(v___x_4674_, 1);
                v_levelParams_4678_ = leanh::lean_ctor_get(v___x_4674_, 2);
                v_nextLevelIdx_4679_ = leanh::lean_ctor_get(v___x_4674_, 3);
                v_levelArgs_4680_ = leanh::lean_ctor_get(v___x_4674_, 4);
                v_newLocalDecls_4681_ = leanh::lean_ctor_get(v___x_4674_, 5);
                v_newLocalDeclsForMVars_4682_ = leanh::lean_ctor_get(v___x_4674_, 6);
                v_newLetDecls_4683_ = leanh::lean_ctor_get(v___x_4674_, 7);
                v_nextExprIdx_4684_ = leanh::lean_ctor_get(v___x_4674_, 8);
                v_exprMVarArgs_4685_ = leanh::lean_ctor_get(v___x_4674_, 9);
                v_exprFVarArgs_4686_ = leanh::lean_ctor_get(v___x_4674_, 10);
                v_toProcess_4687_ = leanh::lean_ctor_get(v___x_4674_, 11);
                v_isSharedCheck_4703_ = (!leanh::lean_is_exclusive(v___x_4674_)) as u8;
                if v_isSharedCheck_4703_ == 0 {
                    v___x_4689_ = v___x_4674_;
                    v_isShared_4690_ = v_isSharedCheck_4703_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toProcess_4687_);
                    leanh::lean_inc(v_exprFVarArgs_4686_);
                    leanh::lean_inc(v_exprMVarArgs_4685_);
                    leanh::lean_inc(v_nextExprIdx_4684_);
                    leanh::lean_inc(v_newLetDecls_4683_);
                    leanh::lean_inc(v_newLocalDeclsForMVars_4682_);
                    leanh::lean_inc(v_newLocalDecls_4681_);
                    leanh::lean_inc(v_levelArgs_4680_);
                    leanh::lean_inc(v_nextLevelIdx_4679_);
                    leanh::lean_inc(v_levelParams_4678_);
                    leanh::lean_inc(v_visitedExpr_4677_);
                    leanh::lean_inc(v_visitedLevel_4676_);
                    leanh::lean_dec(v___x_4674_);
                    v___x_4689_ = leanh::lean_box(0);
                    v_isShared_4690_ = v_isSharedCheck_4703_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4691_ = l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__1;
                v___x_4692_ = lean_name_append_index_after(v___x_4691_, v_nextLevelIdx_4675_);
                leanh::lean_inc(v___x_4692_);
                v___x_4693_ = lean_array_push(v_levelParams_4678_, v___x_4692_);
                v___x_4694_ = leanh::lean_unsigned_to_nat(1);
                v___x_4695_ = lean_nat_add(v_nextLevelIdx_4679_, v___x_4694_);
                leanh::lean_dec(v_nextLevelIdx_4679_);
                v___x_4696_ = lean_array_push(v_levelArgs_4680_, v_u_4670_);
                if v_isShared_4690_ == 0 {
                    leanh::lean_ctor_set(v___x_4689_, 4, v___x_4696_);
                    leanh::lean_ctor_set(v___x_4689_, 3, v___x_4695_);
                    leanh::lean_ctor_set(v___x_4689_, 2, v___x_4693_);
                    v___x_4698_ = v___x_4689_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4702_ = leanh::lean_alloc_ctor(0, 12, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4702_, 0, v_visitedLevel_4676_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4702_, 1, v_visitedExpr_4677_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4702_, 2, v___x_4693_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4702_, 3, v___x_4695_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4702_, 4, v___x_4696_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4702_, 5, v_newLocalDecls_4681_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4702_,
                        6,
                        v_newLocalDeclsForMVars_4682_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4702_, 7, v_newLetDecls_4683_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4702_, 8, v_nextExprIdx_4684_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4702_, 9, v_exprMVarArgs_4685_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4702_, 10, v_exprFVarArgs_4686_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4702_, 11, v_toProcess_4687_);
                    v___x_4698_ = v_reuseFailAlloc_4702_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4699_ = lean_st_ref_set(v_a_4671_, v___x_4698_);
                v___x_4700_ = l_Lean_mkLevelParam(v___x_4692_);
                v___x_4701_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4701_, 0, v___x_4700_);
                return v___x_4701_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Closure_mkNewLevelParam___redArg___boxed(
    mut v_u_4704_: *mut leanh::LeanObject,
    mut v_a_4705_: *mut leanh::LeanObject,
    mut v_a_4706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4707_ = l_Lean_Meta_Closure_mkNewLevelParam___redArg(v_u_4704_, v_a_4705_);
    leanh::lean_dec(v_a_4705_);
    return v_res_4707_;
}
pub unsafe fn l_Lean_Meta_Closure_mkNewLevelParam(
    mut v_u_4708_: *mut leanh::LeanObject,
    mut v_a_4709_: u8,
    mut v_a_4710_: *mut leanh::LeanObject,
    mut v_a_4711_: *mut leanh::LeanObject,
    mut v_a_4712_: *mut leanh::LeanObject,
    mut v_a_4713_: *mut leanh::LeanObject,
    mut v_a_4714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4716_ = l_Lean_Meta_Closure_mkNewLevelParam___redArg(v_u_4708_, v_a_4710_);
    return v___x_4716_;
}
pub unsafe fn l_Lean_Meta_Closure_mkNewLevelParam___boxed(
    mut v_u_4717_: *mut leanh::LeanObject,
    mut v_a_4718_: *mut leanh::LeanObject,
    mut v_a_4719_: *mut leanh::LeanObject,
    mut v_a_4720_: *mut leanh::LeanObject,
    mut v_a_4721_: *mut leanh::LeanObject,
    mut v_a_4722_: *mut leanh::LeanObject,
    mut v_a_4723_: *mut leanh::LeanObject,
    mut v_a_4724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_4725_: u8 = 0;
    let mut v_res_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_4725_ = (leanh::lean_unbox(v_a_4718_) as u8);
    v_res_4726_ = l_Lean_Meta_Closure_mkNewLevelParam(
        v_u_4717_,
        v_a_boxed_4725_,
        v_a_4719_,
        v_a_4720_,
        v_a_4721_,
        v_a_4722_,
        v_a_4723_,
    );
    leanh::lean_dec(v_a_4723_);
    leanh::lean_dec_ref(v_a_4722_);
    leanh::lean_dec(v_a_4721_);
    leanh::lean_dec_ref(v_a_4720_);
    leanh::lean_dec(v_a_4719_);
    return v_res_4726_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Closure_collectLevelAux_spec__0(
    mut v_msg_4727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4728_ = leanh::lean_box(0);
    v___x_4729_ = lean_panic_fn_borrowed(v___x_4728_, v_msg_4727_);
    return v___x_4729_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(
    mut v_a_4730_: *mut leanh::LeanObject,
    mut v_x_4731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: u8 = 0;
    let mut v___x_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4731_) == 0 {
                    v___x_4732_ = leanh::lean_box(0);
                    return v___x_4732_;
                } else {
                    v_key_4733_ = leanh::lean_ctor_get(v_x_4731_, 0);
                    v_value_4734_ = leanh::lean_ctor_get(v_x_4731_, 1);
                    v_tail_4735_ = leanh::lean_ctor_get(v_x_4731_, 2);
                    v___x_4736_ = lean_level_eq(v_key_4733_, v_a_4730_);
                    if v___x_4736_ == 0 {
                        v_x_4731_ = v_tail_4735_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_4734_);
                        v___x_4738_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4738_, 0, v_value_4734_);
                        return v___x_4738_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg___boxed(
    mut v_a_4739_: *mut leanh::LeanObject,
    mut v_x_4740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4741_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(v_a_4739_, v_x_4740_);
    leanh::lean_dec(v_x_4740_);
    leanh::lean_dec(v_a_4739_);
    return v_res_4741_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(
    mut v_m_4742_: *mut leanh::LeanObject,
    mut v_a_4743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: u64 = 0;
    let mut v___x_4747_: u64 = 0;
    let mut v___x_4748_: u64 = 0;
    let mut v_fold_4749_: u64 = 0;
    let mut v___x_4750_: u64 = 0;
    let mut v___x_4751_: u64 = 0;
    let mut v___x_4752_: u64 = 0;
    let mut v___x_4753_: usize = 0;
    let mut v___x_4754_: usize = 0;
    let mut v___x_4755_: usize = 0;
    let mut v___x_4756_: usize = 0;
    let mut v___x_4757_: usize = 0;
    let mut v___x_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_4744_ = leanh::lean_ctor_get(v_m_4742_, 1);
    v___x_4745_ = lean_array_get_size(v_buckets_4744_);
    v___x_4746_ = l_Lean_Level_hash(v_a_4743_);
    v___x_4747_ = 32u64;
    v___x_4748_ = lean_uint64_shift_right(v___x_4746_, v___x_4747_);
    v_fold_4749_ = lean_uint64_xor(v___x_4746_, v___x_4748_);
    v___x_4750_ = 16u64;
    v___x_4751_ = lean_uint64_shift_right(v_fold_4749_, v___x_4750_);
    v___x_4752_ = lean_uint64_xor(v_fold_4749_, v___x_4751_);
    v___x_4753_ = lean_uint64_to_usize(v___x_4752_);
    v___x_4754_ = lean_usize_of_nat(v___x_4745_);
    v___x_4755_ = 1usize;
    v___x_4756_ = lean_usize_sub(v___x_4754_, v___x_4755_);
    v___x_4757_ = lean_usize_land(v___x_4753_, v___x_4756_);
    v___x_4758_ = lean_array_uget_borrowed(v_buckets_4744_, v___x_4757_);
    v___x_4759_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(v_a_4743_, v___x_4758_);
    return v___x_4759_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg___boxed(
    mut v_m_4760_: *mut leanh::LeanObject,
    mut v_a_4761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4762_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_m_4760_, v_a_4761_);
    leanh::lean_dec(v_a_4761_);
    leanh::lean_dec_ref(v_m_4760_);
    return v_res_4762_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6___redArg(
    mut v_x_4763_: *mut leanh::LeanObject,
    mut v_x_4764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4770_: u8 = 0;
    let mut v___x_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: u64 = 0;
    let mut v___x_4773_: u64 = 0;
    let mut v___x_4774_: u64 = 0;
    let mut v_fold_4775_: u64 = 0;
    let mut v___x_4776_: u64 = 0;
    let mut v___x_4777_: u64 = 0;
    let mut v___x_4778_: u64 = 0;
    let mut v___x_4779_: usize = 0;
    let mut v___x_4780_: usize = 0;
    let mut v___x_4781_: usize = 0;
    let mut v___x_4782_: usize = 0;
    let mut v___x_4783_: usize = 0;
    let mut v___x_4784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4790_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4764_) == 0 {
                    return v_x_4763_;
                } else {
                    v_key_4765_ = leanh::lean_ctor_get(v_x_4764_, 0);
                    v_value_4766_ = leanh::lean_ctor_get(v_x_4764_, 1);
                    v_tail_4767_ = leanh::lean_ctor_get(v_x_4764_, 2);
                    v_isSharedCheck_4790_ = (!leanh::lean_is_exclusive(v_x_4764_)) as u8;
                    if v_isSharedCheck_4790_ == 0 {
                        v___x_4769_ = v_x_4764_;
                        v_isShared_4770_ = v_isSharedCheck_4790_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4767_);
                        leanh::lean_inc(v_value_4766_);
                        leanh::lean_inc(v_key_4765_);
                        leanh::lean_dec(v_x_4764_);
                        v___x_4769_ = leanh::lean_box(0);
                        v_isShared_4770_ = v_isSharedCheck_4790_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4771_ = lean_array_get_size(v_x_4763_);
                v___x_4772_ = l_Lean_Level_hash(v_key_4765_);
                v___x_4773_ = 32u64;
                v___x_4774_ = lean_uint64_shift_right(v___x_4772_, v___x_4773_);
                v_fold_4775_ = lean_uint64_xor(v___x_4772_, v___x_4774_);
                v___x_4776_ = 16u64;
                v___x_4777_ = lean_uint64_shift_right(v_fold_4775_, v___x_4776_);
                v___x_4778_ = lean_uint64_xor(v_fold_4775_, v___x_4777_);
                v___x_4779_ = lean_uint64_to_usize(v___x_4778_);
                v___x_4780_ = lean_usize_of_nat(v___x_4771_);
                v___x_4781_ = 1usize;
                v___x_4782_ = lean_usize_sub(v___x_4780_, v___x_4781_);
                v___x_4783_ = lean_usize_land(v___x_4779_, v___x_4782_);
                v___x_4784_ = lean_array_uget_borrowed(v_x_4763_, v___x_4783_);
                leanh::lean_inc(v___x_4784_);
                if v_isShared_4770_ == 0 {
                    leanh::lean_ctor_set(v___x_4769_, 2, v___x_4784_);
                    v___x_4786_ = v___x_4769_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4789_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4789_, 0, v_key_4765_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4789_, 1, v_value_4766_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4789_, 2, v___x_4784_);
                    v___x_4786_ = v_reuseFailAlloc_4789_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4787_ = lean_array_uset(v_x_4763_, v___x_4783_, v___x_4786_);
                v_x_4763_ = v___x_4787_;
                v_x_4764_ = v_tail_4767_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5___redArg(
    mut v_i_4791_: *mut leanh::LeanObject,
    mut v_source_4792_: *mut leanh::LeanObject,
    mut v_target_4793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: u8 = 0;
    let mut v_es_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4794_ = lean_array_get_size(v_source_4792_);
                v___x_4795_ = lean_nat_dec_lt(v_i_4791_, v___x_4794_);
                if v___x_4795_ == 0 {
                    leanh::lean_dec_ref(v_source_4792_);
                    leanh::lean_dec(v_i_4791_);
                    return v_target_4793_;
                } else {
                    v_es_4796_ = lean_array_fget(v_source_4792_, v_i_4791_);
                    v___x_4797_ = leanh::lean_box(0);
                    v_source_4798_ = lean_array_fset(v_source_4792_, v_i_4791_, v___x_4797_);
                    v_target_4799_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6___redArg(v_target_4793_, v_es_4796_);
                    v___x_4800_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4801_ = lean_nat_add(v_i_4791_, v___x_4800_);
                    leanh::lean_dec(v_i_4791_);
                    v_i_4791_ = v___x_4801_;
                    v_source_4792_ = v_source_4798_;
                    v_target_4793_ = v_target_4799_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4___redArg(
    mut v_data_4803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4804_ = lean_array_get_size(v_data_4803_);
    v___x_4805_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_4806_ = lean_nat_mul(v___x_4804_, v___x_4805_);
    v___x_4807_ = leanh::lean_unsigned_to_nat(0);
    v___x_4808_ = leanh::lean_box(0);
    v___x_4809_ = lean_mk_array(v_nbuckets_4806_, v___x_4808_);
    v___x_4810_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5___redArg(v___x_4807_, v_data_4803_, v___x_4809_);
    return v___x_4810_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(
    mut v_a_4811_: *mut leanh::LeanObject,
    mut v_x_4812_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4813_: u8 = 0;
    let mut v_key_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4812_) == 0 {
                    v___x_4813_ = 0;
                    return v___x_4813_;
                } else {
                    v_key_4814_ = leanh::lean_ctor_get(v_x_4812_, 0);
                    v_tail_4815_ = leanh::lean_ctor_get(v_x_4812_, 2);
                    v___x_4816_ = lean_level_eq(v_key_4814_, v_a_4811_);
                    if v___x_4816_ == 0 {
                        v_x_4812_ = v_tail_4815_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4816_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg___boxed(
    mut v_a_4818_: *mut leanh::LeanObject,
    mut v_x_4819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4820_: u8 = 0;
    let mut v_r_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4820_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(v_a_4818_, v_x_4819_);
    leanh::lean_dec(v_x_4819_);
    leanh::lean_dec(v_a_4818_);
    v_r_4821_ = leanh::lean_box((v_res_4820_) as usize);
    return v_r_4821_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5___redArg(
    mut v_a_4822_: *mut leanh::LeanObject,
    mut v_b_4823_: *mut leanh::LeanObject,
    mut v_x_4824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4830_: u8 = 0;
    let mut v___x_4831_: u8 = 0;
    let mut v___x_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4839_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4824_) == 0 {
                    leanh::lean_dec(v_b_4823_);
                    leanh::lean_dec(v_a_4822_);
                    return v_x_4824_;
                } else {
                    v_key_4825_ = leanh::lean_ctor_get(v_x_4824_, 0);
                    v_value_4826_ = leanh::lean_ctor_get(v_x_4824_, 1);
                    v_tail_4827_ = leanh::lean_ctor_get(v_x_4824_, 2);
                    v_isSharedCheck_4839_ = (!leanh::lean_is_exclusive(v_x_4824_)) as u8;
                    if v_isSharedCheck_4839_ == 0 {
                        v___x_4829_ = v_x_4824_;
                        v_isShared_4830_ = v_isSharedCheck_4839_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4827_);
                        leanh::lean_inc(v_value_4826_);
                        leanh::lean_inc(v_key_4825_);
                        leanh::lean_dec(v_x_4824_);
                        v___x_4829_ = leanh::lean_box(0);
                        v_isShared_4830_ = v_isSharedCheck_4839_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4831_ = lean_level_eq(v_key_4825_, v_a_4822_);
                if v___x_4831_ == 0 {
                    v___x_4832_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5___redArg(v_a_4822_, v_b_4823_, v_tail_4827_);
                    if v_isShared_4830_ == 0 {
                        leanh::lean_ctor_set(v___x_4829_, 2, v___x_4832_);
                        v___x_4834_ = v___x_4829_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4835_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4835_, 0, v_key_4825_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4835_, 1, v_value_4826_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4835_, 2, v___x_4832_);
                        v___x_4834_ = v_reuseFailAlloc_4835_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_4826_);
                    leanh::lean_dec(v_key_4825_);
                    if v_isShared_4830_ == 0 {
                        leanh::lean_ctor_set(v___x_4829_, 1, v_b_4823_);
                        leanh::lean_ctor_set(v___x_4829_, 0, v_a_4822_);
                        v___x_4837_ = v___x_4829_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4838_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4838_, 0, v_a_4822_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4838_, 1, v_b_4823_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4838_, 2, v_tail_4827_);
                        v___x_4837_ = v_reuseFailAlloc_4838_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4834_;
            }
            3 => {
                return v___x_4837_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(
    mut v_m_4840_: *mut leanh::LeanObject,
    mut v_a_4841_: *mut leanh::LeanObject,
    mut v_b_4842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4847_: u8 = 0;
    let mut v___x_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: u64 = 0;
    let mut v___x_4850_: u64 = 0;
    let mut v___x_4851_: u64 = 0;
    let mut v_fold_4852_: u64 = 0;
    let mut v___x_4853_: u64 = 0;
    let mut v___x_4854_: u64 = 0;
    let mut v___x_4855_: u64 = 0;
    let mut v___x_4856_: usize = 0;
    let mut v___x_4857_: usize = 0;
    let mut v___x_4858_: usize = 0;
    let mut v___x_4859_: usize = 0;
    let mut v___x_4860_: usize = 0;
    let mut v_bkt_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: u8 = 0;
    let mut v___x_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: u8 = 0;
    let mut v_val_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4887_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4843_ = leanh::lean_ctor_get(v_m_4840_, 0);
                v_buckets_4844_ = leanh::lean_ctor_get(v_m_4840_, 1);
                v_isSharedCheck_4887_ = (!leanh::lean_is_exclusive(v_m_4840_)) as u8;
                if v_isSharedCheck_4887_ == 0 {
                    v___x_4846_ = v_m_4840_;
                    v_isShared_4847_ = v_isSharedCheck_4887_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_4844_);
                    leanh::lean_inc(v_size_4843_);
                    leanh::lean_dec(v_m_4840_);
                    v___x_4846_ = leanh::lean_box(0);
                    v_isShared_4847_ = v_isSharedCheck_4887_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4848_ = lean_array_get_size(v_buckets_4844_);
                v___x_4849_ = l_Lean_Level_hash(v_a_4841_);
                v___x_4850_ = 32u64;
                v___x_4851_ = lean_uint64_shift_right(v___x_4849_, v___x_4850_);
                v_fold_4852_ = lean_uint64_xor(v___x_4849_, v___x_4851_);
                v___x_4853_ = 16u64;
                v___x_4854_ = lean_uint64_shift_right(v_fold_4852_, v___x_4853_);
                v___x_4855_ = lean_uint64_xor(v_fold_4852_, v___x_4854_);
                v___x_4856_ = lean_uint64_to_usize(v___x_4855_);
                v___x_4857_ = lean_usize_of_nat(v___x_4848_);
                v___x_4858_ = 1usize;
                v___x_4859_ = lean_usize_sub(v___x_4857_, v___x_4858_);
                v___x_4860_ = lean_usize_land(v___x_4856_, v___x_4859_);
                v_bkt_4861_ = lean_array_uget_borrowed(v_buckets_4844_, v___x_4860_);
                v___x_4862_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(v_a_4841_, v_bkt_4861_);
                if v___x_4862_ == 0 {
                    v___x_4863_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_4864_ = lean_nat_add(v_size_4843_, v___x_4863_);
                    leanh::lean_dec(v_size_4843_);
                    leanh::lean_inc(v_bkt_4861_);
                    v___x_4865_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_4865_, 0, v_a_4841_);
                    leanh::lean_ctor_set(v___x_4865_, 1, v_b_4842_);
                    leanh::lean_ctor_set(v___x_4865_, 2, v_bkt_4861_);
                    v_buckets_x27_4866_ =
                        lean_array_uset(v_buckets_4844_, v___x_4860_, v___x_4865_);
                    v___x_4867_ = leanh::lean_unsigned_to_nat(4);
                    v___x_4868_ = lean_nat_mul(v_size_x27_4864_, v___x_4867_);
                    v___x_4869_ = leanh::lean_unsigned_to_nat(3);
                    v___x_4870_ = lean_nat_div(v___x_4868_, v___x_4869_);
                    leanh::lean_dec(v___x_4868_);
                    v___x_4871_ = lean_array_get_size(v_buckets_x27_4866_);
                    v___x_4872_ = lean_nat_dec_le(v___x_4870_, v___x_4871_);
                    leanh::lean_dec(v___x_4870_);
                    if v___x_4872_ == 0 {
                        v_val_4873_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4___redArg(v_buckets_x27_4866_);
                        if v_isShared_4847_ == 0 {
                            leanh::lean_ctor_set(v___x_4846_, 1, v_val_4873_);
                            leanh::lean_ctor_set(v___x_4846_, 0, v_size_x27_4864_);
                            v___x_4875_ = v___x_4846_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4876_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_4876_,
                                0,
                                v_size_x27_4864_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_4876_, 1, v_val_4873_);
                            v___x_4875_ = v_reuseFailAlloc_4876_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_4847_ == 0 {
                            leanh::lean_ctor_set(v___x_4846_, 1, v_buckets_x27_4866_);
                            leanh::lean_ctor_set(v___x_4846_, 0, v_size_x27_4864_);
                            v___x_4878_ = v___x_4846_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4879_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_4879_,
                                0,
                                v_size_x27_4864_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_4879_,
                                1,
                                v_buckets_x27_4866_,
                            );
                            v___x_4878_ = v_reuseFailAlloc_4879_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_4861_);
                    v___x_4880_ = leanh::lean_box(0);
                    v_buckets_x27_4881_ =
                        lean_array_uset(v_buckets_4844_, v___x_4860_, v___x_4880_);
                    v___x_4882_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5___redArg(v_a_4841_, v_b_4842_, v_bkt_4861_);
                    v___x_4883_ = lean_array_uset(v_buckets_x27_4881_, v___x_4860_, v___x_4882_);
                    if v_isShared_4847_ == 0 {
                        leanh::lean_ctor_set(v___x_4846_, 1, v___x_4883_);
                        v___x_4885_ = v___x_4846_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4886_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4886_, 0, v_size_4843_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4886_, 1, v___x_4883_);
                        v___x_4885_ = v_reuseFailAlloc_4886_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4875_;
            }
            3 => {
                return v___x_4878_;
            }
            4 => {
                return v___x_4885_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Closure_collectLevelAux___redArg(
    mut v_x_4888_: *mut leanh::LeanObject,
    mut v_a_4889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4894_: u8 = 0;
    let mut v___x_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4902_: u8 = 0;
    let mut v___x_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: usize = 0;
    let mut v___x_4912_: usize = 0;
    let mut v___x_4913_: u8 = 0;
    let mut v___x_4914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_4919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_4924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextLevelIdx_4927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelArgs_4928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDecls_4929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDeclsForMVars_4930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLetDecls_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextExprIdx_4932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprMVarArgs_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprFVarArgs_4934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toProcess_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4938_: u8 = 0;
    let mut v___x_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4944_: u8 = 0;
    let mut v_a_4945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: u8 = 0;
    let mut v___x_4948_: u8 = 0;
    let mut v_a_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: usize = 0;
    let mut v___x_4955_: usize = 0;
    let mut v___x_4956_: u8 = 0;
    let mut v___x_4957_: usize = 0;
    let mut v___x_4958_: usize = 0;
    let mut v___x_4959_: u8 = 0;
    let mut v___y_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_4963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_4968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_4969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextLevelIdx_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelArgs_4972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDecls_4973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDeclsForMVars_4974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLetDecls_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextExprIdx_4976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprMVarArgs_4977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprFVarArgs_4978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toProcess_4979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4982_: u8 = 0;
    let mut v___x_4983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4988_: u8 = 0;
    let mut v_a_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: u8 = 0;
    let mut v___x_4994_: u8 = 0;
    let mut v___x_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_4997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextLevelIdx_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelArgs_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDecls_5007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDeclsForMVars_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLetDecls_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextExprIdx_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprMVarArgs_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprFVarArgs_5012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toProcess_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5016_: u8 = 0;
    let mut v___x_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5022_: u8 = 0;
    let mut v_a_5023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: u8 = 0;
    let mut v___x_5026_: u8 = 0;
    let mut v_a_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: usize = 0;
    let mut v___x_5033_: usize = 0;
    let mut v___x_5034_: u8 = 0;
    let mut v___x_5035_: usize = 0;
    let mut v___x_5036_: usize = 0;
    let mut v___x_5037_: u8 = 0;
    let mut v___y_5039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_5041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_5047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextLevelIdx_5049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelArgs_5050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDecls_5051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDeclsForMVars_5052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLetDecls_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextExprIdx_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprMVarArgs_5055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprFVarArgs_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toProcess_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5060_: u8 = 0;
    let mut v___x_5061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5066_: u8 = 0;
    let mut v_a_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: u8 = 0;
    let mut v___x_5072_: u8 = 0;
    let mut v___x_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_5075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_5081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_5082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextLevelIdx_5083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelArgs_5084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDecls_5085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDeclsForMVars_5086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLetDecls_5087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextExprIdx_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprMVarArgs_5089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprFVarArgs_5090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toProcess_5091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5094_: u8 = 0;
    let mut v___x_5095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5100_: u8 = 0;
    let mut v_a_5101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: u8 = 0;
    let mut v___x_5104_: u8 = 0;
    let mut v___x_5105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_4888_) {
                0 => {
                    v___x_4907_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4907_, 0, v_x_4888_);
                    return v___x_4907_;
                }
                1 => {
                    v_a_4908_ = leanh::lean_ctor_get(v_x_4888_, 0);
                    v___x_4947_ = l_Lean_Level_hasMVar(v_a_4908_);
                    if v___x_4947_ == 0 {
                        v___x_4948_ = l_Lean_Level_hasParam(v_a_4908_);
                        if v___x_4948_ == 0 {
                            leanh::lean_inc(v_a_4908_);
                            v_a_4910_ = v_a_4908_;
                            state = 3;
                            continue;
                        } else {
                            state = 4;
                            continue;
                        }
                    } else {
                        state = 4;
                        continue;
                    }
                }
                2 => {
                    v_a_4949_ = leanh::lean_ctor_get(v_x_4888_, 0);
                    v_a_4950_ = leanh::lean_ctor_get(v_x_4888_, 1);
                    v___x_5025_ = l_Lean_Level_hasMVar(v_a_4949_);
                    if v___x_5025_ == 0 {
                        v___x_5026_ = l_Lean_Level_hasParam(v_a_4949_);
                        if v___x_5026_ == 0 {
                            leanh::lean_inc(v_a_4949_);
                            v_a_4992_ = v_a_4949_;
                            state = 11;
                            continue;
                        } else {
                            state = 12;
                            continue;
                        }
                    } else {
                        state = 12;
                        continue;
                    }
                }
                3 => {
                    v_a_5027_ = leanh::lean_ctor_get(v_x_4888_, 0);
                    v_a_5028_ = leanh::lean_ctor_get(v_x_4888_, 1);
                    v___x_5103_ = l_Lean_Level_hasMVar(v_a_5027_);
                    if v___x_5103_ == 0 {
                        v___x_5104_ = l_Lean_Level_hasParam(v_a_5027_);
                        if v___x_5104_ == 0 {
                            leanh::lean_inc(v_a_5027_);
                            v_a_5070_ = v_a_5027_;
                            state = 19;
                            continue;
                        } else {
                            state = 20;
                            continue;
                        }
                    } else {
                        state = 20;
                        continue;
                    }
                }
                _ => {
                    v___x_5105_ =
                        l_Lean_Meta_Closure_mkNewLevelParam___redArg(v_x_4888_, v_a_4889_);
                    return v___x_5105_;
                }
            },
            1 => {
                if v___y_4894_ == 0 {
                    leanh::lean_dec(v_x_4888_);
                    v___x_4895_ = l_Lean_mkLevelMax_x27(v___y_4893_, v___y_4892_);
                    v___x_4896_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4896_, 0, v___x_4895_);
                    return v___x_4896_;
                } else {
                    v___x_4897_ = l_Lean_simpLevelMax_x27(v___y_4893_, v___y_4892_, v_x_4888_);
                    leanh::lean_dec(v_x_4888_);
                    leanh::lean_dec(v___y_4892_);
                    leanh::lean_dec(v___y_4893_);
                    v___x_4898_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4898_, 0, v___x_4897_);
                    return v___x_4898_;
                }
            }
            2 => {
                if v___y_4902_ == 0 {
                    leanh::lean_dec(v_x_4888_);
                    v___x_4903_ = l_Lean_mkLevelIMax_x27(v___y_4901_, v___y_4900_);
                    v___x_4904_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4904_, 0, v___x_4903_);
                    return v___x_4904_;
                } else {
                    v___x_4905_ = l_Lean_simpLevelIMax_x27(v___y_4901_, v___y_4900_, v_x_4888_);
                    leanh::lean_dec(v_x_4888_);
                    v___x_4906_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4906_, 0, v___x_4905_);
                    return v___x_4906_;
                }
            }
            3 => {
                v___x_4911_ = lean_ptr_addr(v_a_4908_);
                v___x_4912_ = lean_ptr_addr(v_a_4910_);
                v___x_4913_ = lean_usize_dec_eq(v___x_4911_, v___x_4912_);
                if v___x_4913_ == 0 {
                    leanh::lean_dec_ref_known(v_x_4888_, 1);
                    v___x_4914_ = l_Lean_Level_succ___override(v_a_4910_);
                    v___x_4915_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4915_, 0, v___x_4914_);
                    return v___x_4915_;
                } else {
                    leanh::lean_dec(v_a_4910_);
                    v___x_4916_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4916_, 0, v_x_4888_);
                    return v___x_4916_;
                }
            }
            4 => {
                v___x_4918_ = lean_st_ref_get(v_a_4889_);
                v_visitedLevel_4919_ = leanh::lean_ctor_get(v___x_4918_, 0);
                leanh::lean_inc_ref(v_visitedLevel_4919_);
                leanh::lean_dec(v___x_4918_);
                v___x_4920_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_4919_, v_a_4908_);
                leanh::lean_dec_ref(v_visitedLevel_4919_);
                if leanh::lean_obj_tag(v___x_4920_) == 0 {
                    leanh::lean_inc(v_a_4908_);
                    v___x_4921_ =
                        l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_4908_, v_a_4889_);
                    if leanh::lean_obj_tag(v___x_4921_) == 0 {
                        v_a_4922_ = leanh::lean_ctor_get(v___x_4921_, 0);
                        leanh::lean_inc(v_a_4922_);
                        leanh::lean_dec_ref_known(v___x_4921_, 1);
                        v___x_4923_ = lean_st_ref_take(v_a_4889_);
                        v_visitedLevel_4924_ = leanh::lean_ctor_get(v___x_4923_, 0);
                        v_visitedExpr_4925_ = leanh::lean_ctor_get(v___x_4923_, 1);
                        v_levelParams_4926_ = leanh::lean_ctor_get(v___x_4923_, 2);
                        v_nextLevelIdx_4927_ = leanh::lean_ctor_get(v___x_4923_, 3);
                        v_levelArgs_4928_ = leanh::lean_ctor_get(v___x_4923_, 4);
                        v_newLocalDecls_4929_ = leanh::lean_ctor_get(v___x_4923_, 5);
                        v_newLocalDeclsForMVars_4930_ = leanh::lean_ctor_get(v___x_4923_, 6);
                        v_newLetDecls_4931_ = leanh::lean_ctor_get(v___x_4923_, 7);
                        v_nextExprIdx_4932_ = leanh::lean_ctor_get(v___x_4923_, 8);
                        v_exprMVarArgs_4933_ = leanh::lean_ctor_get(v___x_4923_, 9);
                        v_exprFVarArgs_4934_ = leanh::lean_ctor_get(v___x_4923_, 10);
                        v_toProcess_4935_ = leanh::lean_ctor_get(v___x_4923_, 11);
                        v_isSharedCheck_4944_ =
                            (!leanh::lean_is_exclusive(v___x_4923_)) as u8;
                        if v_isSharedCheck_4944_ == 0 {
                            v___x_4937_ = v___x_4923_;
                            v_isShared_4938_ = v_isSharedCheck_4944_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_toProcess_4935_);
                            leanh::lean_inc(v_exprFVarArgs_4934_);
                            leanh::lean_inc(v_exprMVarArgs_4933_);
                            leanh::lean_inc(v_nextExprIdx_4932_);
                            leanh::lean_inc(v_newLetDecls_4931_);
                            leanh::lean_inc(v_newLocalDeclsForMVars_4930_);
                            leanh::lean_inc(v_newLocalDecls_4929_);
                            leanh::lean_inc(v_levelArgs_4928_);
                            leanh::lean_inc(v_nextLevelIdx_4927_);
                            leanh::lean_inc(v_levelParams_4926_);
                            leanh::lean_inc(v_visitedExpr_4925_);
                            leanh::lean_inc(v_visitedLevel_4924_);
                            leanh::lean_dec(v___x_4923_);
                            v___x_4937_ = leanh::lean_box(0);
                            v_isShared_4938_ = v_isSharedCheck_4944_;
                            state = 5;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v___x_4921_) == 0 {
                            v_a_4945_ = leanh::lean_ctor_get(v___x_4921_, 0);
                            leanh::lean_inc(v_a_4945_);
                            leanh::lean_dec_ref_known(v___x_4921_, 1);
                            v_a_4910_ = v_a_4945_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec_ref_known(v_x_4888_, 1);
                            return v___x_4921_;
                        }
                    }
                } else {
                    v_val_4946_ = leanh::lean_ctor_get(v___x_4920_, 0);
                    leanh::lean_inc(v_val_4946_);
                    leanh::lean_dec_ref_known(v___x_4920_, 1);
                    v_a_4910_ = v_val_4946_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc(v_a_4922_);
                leanh::lean_inc(v_a_4908_);
                v___x_4939_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_4924_, v_a_4908_, v_a_4922_);
                if v_isShared_4938_ == 0 {
                    leanh::lean_ctor_set(v___x_4937_, 0, v___x_4939_);
                    v___x_4941_ = v___x_4937_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4943_ = leanh::lean_alloc_ctor(0, 12, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4943_, 0, v___x_4939_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4943_, 1, v_visitedExpr_4925_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4943_, 2, v_levelParams_4926_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4943_, 3, v_nextLevelIdx_4927_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4943_, 4, v_levelArgs_4928_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4943_, 5, v_newLocalDecls_4929_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4943_,
                        6,
                        v_newLocalDeclsForMVars_4930_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4943_, 7, v_newLetDecls_4931_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4943_, 8, v_nextExprIdx_4932_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4943_, 9, v_exprMVarArgs_4933_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4943_, 10, v_exprFVarArgs_4934_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4943_, 11, v_toProcess_4935_);
                    v___x_4941_ = v_reuseFailAlloc_4943_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4942_ = lean_st_ref_set(v_a_4889_, v___x_4941_);
                v_a_4910_ = v_a_4922_;
                state = 3;
                continue;
            }
            7 => {
                v___x_4954_ = lean_ptr_addr(v_a_4949_);
                v___x_4955_ = lean_ptr_addr(v___y_4952_);
                v___x_4956_ = lean_usize_dec_eq(v___x_4954_, v___x_4955_);
                if v___x_4956_ == 0 {
                    v___y_4892_ = v_a_4953_;
                    v___y_4893_ = v___y_4952_;
                    v___y_4894_ = v___x_4956_;
                    state = 1;
                    continue;
                } else {
                    v___x_4957_ = lean_ptr_addr(v_a_4950_);
                    v___x_4958_ = lean_ptr_addr(v_a_4953_);
                    v___x_4959_ = lean_usize_dec_eq(v___x_4957_, v___x_4958_);
                    v___y_4892_ = v_a_4953_;
                    v___y_4893_ = v___y_4952_;
                    v___y_4894_ = v___x_4959_;
                    state = 1;
                    continue;
                }
            }
            8 => {
                v___x_4962_ = lean_st_ref_get(v_a_4889_);
                v_visitedLevel_4963_ = leanh::lean_ctor_get(v___x_4962_, 0);
                leanh::lean_inc_ref(v_visitedLevel_4963_);
                leanh::lean_dec(v___x_4962_);
                v___x_4964_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_4963_, v_a_4950_);
                leanh::lean_dec_ref(v_visitedLevel_4963_);
                if leanh::lean_obj_tag(v___x_4964_) == 0 {
                    leanh::lean_inc(v_a_4950_);
                    v___x_4965_ =
                        l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_4950_, v_a_4889_);
                    if leanh::lean_obj_tag(v___x_4965_) == 0 {
                        v_a_4966_ = leanh::lean_ctor_get(v___x_4965_, 0);
                        leanh::lean_inc(v_a_4966_);
                        leanh::lean_dec_ref_known(v___x_4965_, 1);
                        v___x_4967_ = lean_st_ref_take(v_a_4889_);
                        v_visitedLevel_4968_ = leanh::lean_ctor_get(v___x_4967_, 0);
                        v_visitedExpr_4969_ = leanh::lean_ctor_get(v___x_4967_, 1);
                        v_levelParams_4970_ = leanh::lean_ctor_get(v___x_4967_, 2);
                        v_nextLevelIdx_4971_ = leanh::lean_ctor_get(v___x_4967_, 3);
                        v_levelArgs_4972_ = leanh::lean_ctor_get(v___x_4967_, 4);
                        v_newLocalDecls_4973_ = leanh::lean_ctor_get(v___x_4967_, 5);
                        v_newLocalDeclsForMVars_4974_ = leanh::lean_ctor_get(v___x_4967_, 6);
                        v_newLetDecls_4975_ = leanh::lean_ctor_get(v___x_4967_, 7);
                        v_nextExprIdx_4976_ = leanh::lean_ctor_get(v___x_4967_, 8);
                        v_exprMVarArgs_4977_ = leanh::lean_ctor_get(v___x_4967_, 9);
                        v_exprFVarArgs_4978_ = leanh::lean_ctor_get(v___x_4967_, 10);
                        v_toProcess_4979_ = leanh::lean_ctor_get(v___x_4967_, 11);
                        v_isSharedCheck_4988_ =
                            (!leanh::lean_is_exclusive(v___x_4967_)) as u8;
                        if v_isSharedCheck_4988_ == 0 {
                            v___x_4981_ = v___x_4967_;
                            v_isShared_4982_ = v_isSharedCheck_4988_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_toProcess_4979_);
                            leanh::lean_inc(v_exprFVarArgs_4978_);
                            leanh::lean_inc(v_exprMVarArgs_4977_);
                            leanh::lean_inc(v_nextExprIdx_4976_);
                            leanh::lean_inc(v_newLetDecls_4975_);
                            leanh::lean_inc(v_newLocalDeclsForMVars_4974_);
                            leanh::lean_inc(v_newLocalDecls_4973_);
                            leanh::lean_inc(v_levelArgs_4972_);
                            leanh::lean_inc(v_nextLevelIdx_4971_);
                            leanh::lean_inc(v_levelParams_4970_);
                            leanh::lean_inc(v_visitedExpr_4969_);
                            leanh::lean_inc(v_visitedLevel_4968_);
                            leanh::lean_dec(v___x_4967_);
                            v___x_4981_ = leanh::lean_box(0);
                            v_isShared_4982_ = v_isSharedCheck_4988_;
                            state = 9;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v___x_4965_) == 0 {
                            v_a_4989_ = leanh::lean_ctor_get(v___x_4965_, 0);
                            leanh::lean_inc(v_a_4989_);
                            leanh::lean_dec_ref_known(v___x_4965_, 1);
                            v___y_4952_ = v___y_4961_;
                            v_a_4953_ = v_a_4989_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_dec(v___y_4961_);
                            leanh::lean_dec_ref_known(v_x_4888_, 2);
                            return v___x_4965_;
                        }
                    }
                } else {
                    v_val_4990_ = leanh::lean_ctor_get(v___x_4964_, 0);
                    leanh::lean_inc(v_val_4990_);
                    leanh::lean_dec_ref_known(v___x_4964_, 1);
                    v___y_4952_ = v___y_4961_;
                    v_a_4953_ = v_val_4990_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                leanh::lean_inc(v_a_4966_);
                leanh::lean_inc(v_a_4950_);
                v___x_4983_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_4968_, v_a_4950_, v_a_4966_);
                if v_isShared_4982_ == 0 {
                    leanh::lean_ctor_set(v___x_4981_, 0, v___x_4983_);
                    v___x_4985_ = v___x_4981_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4987_ = leanh::lean_alloc_ctor(0, 12, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4987_, 0, v___x_4983_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4987_, 1, v_visitedExpr_4969_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4987_, 2, v_levelParams_4970_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4987_, 3, v_nextLevelIdx_4971_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4987_, 4, v_levelArgs_4972_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4987_, 5, v_newLocalDecls_4973_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4987_,
                        6,
                        v_newLocalDeclsForMVars_4974_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4987_, 7, v_newLetDecls_4975_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4987_, 8, v_nextExprIdx_4976_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4987_, 9, v_exprMVarArgs_4977_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4987_, 10, v_exprFVarArgs_4978_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4987_, 11, v_toProcess_4979_);
                    v___x_4985_ = v_reuseFailAlloc_4987_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_4986_ = lean_st_ref_set(v_a_4889_, v___x_4985_);
                v___y_4952_ = v___y_4961_;
                v_a_4953_ = v_a_4966_;
                state = 7;
                continue;
            }
            11 => {
                v___x_4993_ = l_Lean_Level_hasMVar(v_a_4950_);
                if v___x_4993_ == 0 {
                    v___x_4994_ = l_Lean_Level_hasParam(v_a_4950_);
                    if v___x_4994_ == 0 {
                        leanh::lean_inc(v_a_4950_);
                        v___y_4952_ = v_a_4992_;
                        v_a_4953_ = v_a_4950_;
                        state = 7;
                        continue;
                    } else {
                        v___y_4961_ = v_a_4992_;
                        state = 8;
                        continue;
                    }
                } else {
                    v___y_4961_ = v_a_4992_;
                    state = 8;
                    continue;
                }
            }
            12 => {
                v___x_4996_ = lean_st_ref_get(v_a_4889_);
                v_visitedLevel_4997_ = leanh::lean_ctor_get(v___x_4996_, 0);
                leanh::lean_inc_ref(v_visitedLevel_4997_);
                leanh::lean_dec(v___x_4996_);
                v___x_4998_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_4997_, v_a_4949_);
                leanh::lean_dec_ref(v_visitedLevel_4997_);
                if leanh::lean_obj_tag(v___x_4998_) == 0 {
                    leanh::lean_inc(v_a_4949_);
                    v___x_4999_ =
                        l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_4949_, v_a_4889_);
                    if leanh::lean_obj_tag(v___x_4999_) == 0 {
                        v_a_5000_ = leanh::lean_ctor_get(v___x_4999_, 0);
                        leanh::lean_inc(v_a_5000_);
                        leanh::lean_dec_ref_known(v___x_4999_, 1);
                        v___x_5001_ = lean_st_ref_take(v_a_4889_);
                        v_visitedLevel_5002_ = leanh::lean_ctor_get(v___x_5001_, 0);
                        v_visitedExpr_5003_ = leanh::lean_ctor_get(v___x_5001_, 1);
                        v_levelParams_5004_ = leanh::lean_ctor_get(v___x_5001_, 2);
                        v_nextLevelIdx_5005_ = leanh::lean_ctor_get(v___x_5001_, 3);
                        v_levelArgs_5006_ = leanh::lean_ctor_get(v___x_5001_, 4);
                        v_newLocalDecls_5007_ = leanh::lean_ctor_get(v___x_5001_, 5);
                        v_newLocalDeclsForMVars_5008_ = leanh::lean_ctor_get(v___x_5001_, 6);
                        v_newLetDecls_5009_ = leanh::lean_ctor_get(v___x_5001_, 7);
                        v_nextExprIdx_5010_ = leanh::lean_ctor_get(v___x_5001_, 8);
                        v_exprMVarArgs_5011_ = leanh::lean_ctor_get(v___x_5001_, 9);
                        v_exprFVarArgs_5012_ = leanh::lean_ctor_get(v___x_5001_, 10);
                        v_toProcess_5013_ = leanh::lean_ctor_get(v___x_5001_, 11);
                        v_isSharedCheck_5022_ =
                            (!leanh::lean_is_exclusive(v___x_5001_)) as u8;
                        if v_isSharedCheck_5022_ == 0 {
                            v___x_5015_ = v___x_5001_;
                            v_isShared_5016_ = v_isSharedCheck_5022_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_toProcess_5013_);
                            leanh::lean_inc(v_exprFVarArgs_5012_);
                            leanh::lean_inc(v_exprMVarArgs_5011_);
                            leanh::lean_inc(v_nextExprIdx_5010_);
                            leanh::lean_inc(v_newLetDecls_5009_);
                            leanh::lean_inc(v_newLocalDeclsForMVars_5008_);
                            leanh::lean_inc(v_newLocalDecls_5007_);
                            leanh::lean_inc(v_levelArgs_5006_);
                            leanh::lean_inc(v_nextLevelIdx_5005_);
                            leanh::lean_inc(v_levelParams_5004_);
                            leanh::lean_inc(v_visitedExpr_5003_);
                            leanh::lean_inc(v_visitedLevel_5002_);
                            leanh::lean_dec(v___x_5001_);
                            v___x_5015_ = leanh::lean_box(0);
                            v_isShared_5016_ = v_isSharedCheck_5022_;
                            state = 13;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v___x_4999_) == 0 {
                            v_a_5023_ = leanh::lean_ctor_get(v___x_4999_, 0);
                            leanh::lean_inc(v_a_5023_);
                            leanh::lean_dec_ref_known(v___x_4999_, 1);
                            v_a_4992_ = v_a_5023_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_dec_ref_known(v_x_4888_, 2);
                            return v___x_4999_;
                        }
                    }
                } else {
                    v_val_5024_ = leanh::lean_ctor_get(v___x_4998_, 0);
                    leanh::lean_inc(v_val_5024_);
                    leanh::lean_dec_ref_known(v___x_4998_, 1);
                    v_a_4992_ = v_val_5024_;
                    state = 11;
                    continue;
                }
            }
            13 => {
                leanh::lean_inc(v_a_5000_);
                leanh::lean_inc(v_a_4949_);
                v___x_5017_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_5002_, v_a_4949_, v_a_5000_);
                if v_isShared_5016_ == 0 {
                    leanh::lean_ctor_set(v___x_5015_, 0, v___x_5017_);
                    v___x_5019_ = v___x_5015_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5021_ = leanh::lean_alloc_ctor(0, 12, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5021_, 0, v___x_5017_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5021_, 1, v_visitedExpr_5003_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5021_, 2, v_levelParams_5004_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5021_, 3, v_nextLevelIdx_5005_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5021_, 4, v_levelArgs_5006_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5021_, 5, v_newLocalDecls_5007_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5021_,
                        6,
                        v_newLocalDeclsForMVars_5008_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5021_, 7, v_newLetDecls_5009_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5021_, 8, v_nextExprIdx_5010_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5021_, 9, v_exprMVarArgs_5011_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5021_, 10, v_exprFVarArgs_5012_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5021_, 11, v_toProcess_5013_);
                    v___x_5019_ = v_reuseFailAlloc_5021_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_5020_ = lean_st_ref_set(v_a_4889_, v___x_5019_);
                v_a_4992_ = v_a_5000_;
                state = 11;
                continue;
            }
            15 => {
                v___x_5032_ = lean_ptr_addr(v_a_5027_);
                v___x_5033_ = lean_ptr_addr(v___y_5030_);
                v___x_5034_ = lean_usize_dec_eq(v___x_5032_, v___x_5033_);
                if v___x_5034_ == 0 {
                    v___y_4900_ = v_a_5031_;
                    v___y_4901_ = v___y_5030_;
                    v___y_4902_ = v___x_5034_;
                    state = 2;
                    continue;
                } else {
                    v___x_5035_ = lean_ptr_addr(v_a_5028_);
                    v___x_5036_ = lean_ptr_addr(v_a_5031_);
                    v___x_5037_ = lean_usize_dec_eq(v___x_5035_, v___x_5036_);
                    v___y_4900_ = v_a_5031_;
                    v___y_4901_ = v___y_5030_;
                    v___y_4902_ = v___x_5037_;
                    state = 2;
                    continue;
                }
            }
            16 => {
                v___x_5040_ = lean_st_ref_get(v_a_4889_);
                v_visitedLevel_5041_ = leanh::lean_ctor_get(v___x_5040_, 0);
                leanh::lean_inc_ref(v_visitedLevel_5041_);
                leanh::lean_dec(v___x_5040_);
                v___x_5042_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_5041_, v_a_5028_);
                leanh::lean_dec_ref(v_visitedLevel_5041_);
                if leanh::lean_obj_tag(v___x_5042_) == 0 {
                    leanh::lean_inc(v_a_5028_);
                    v___x_5043_ =
                        l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_5028_, v_a_4889_);
                    if leanh::lean_obj_tag(v___x_5043_) == 0 {
                        v_a_5044_ = leanh::lean_ctor_get(v___x_5043_, 0);
                        leanh::lean_inc(v_a_5044_);
                        leanh::lean_dec_ref_known(v___x_5043_, 1);
                        v___x_5045_ = lean_st_ref_take(v_a_4889_);
                        v_visitedLevel_5046_ = leanh::lean_ctor_get(v___x_5045_, 0);
                        v_visitedExpr_5047_ = leanh::lean_ctor_get(v___x_5045_, 1);
                        v_levelParams_5048_ = leanh::lean_ctor_get(v___x_5045_, 2);
                        v_nextLevelIdx_5049_ = leanh::lean_ctor_get(v___x_5045_, 3);
                        v_levelArgs_5050_ = leanh::lean_ctor_get(v___x_5045_, 4);
                        v_newLocalDecls_5051_ = leanh::lean_ctor_get(v___x_5045_, 5);
                        v_newLocalDeclsForMVars_5052_ = leanh::lean_ctor_get(v___x_5045_, 6);
                        v_newLetDecls_5053_ = leanh::lean_ctor_get(v___x_5045_, 7);
                        v_nextExprIdx_5054_ = leanh::lean_ctor_get(v___x_5045_, 8);
                        v_exprMVarArgs_5055_ = leanh::lean_ctor_get(v___x_5045_, 9);
                        v_exprFVarArgs_5056_ = leanh::lean_ctor_get(v___x_5045_, 10);
                        v_toProcess_5057_ = leanh::lean_ctor_get(v___x_5045_, 11);
                        v_isSharedCheck_5066_ =
                            (!leanh::lean_is_exclusive(v___x_5045_)) as u8;
                        if v_isSharedCheck_5066_ == 0 {
                            v___x_5059_ = v___x_5045_;
                            v_isShared_5060_ = v_isSharedCheck_5066_;
                            state = 17;
                            continue;
                        } else {
                            leanh::lean_inc(v_toProcess_5057_);
                            leanh::lean_inc(v_exprFVarArgs_5056_);
                            leanh::lean_inc(v_exprMVarArgs_5055_);
                            leanh::lean_inc(v_nextExprIdx_5054_);
                            leanh::lean_inc(v_newLetDecls_5053_);
                            leanh::lean_inc(v_newLocalDeclsForMVars_5052_);
                            leanh::lean_inc(v_newLocalDecls_5051_);
                            leanh::lean_inc(v_levelArgs_5050_);
                            leanh::lean_inc(v_nextLevelIdx_5049_);
                            leanh::lean_inc(v_levelParams_5048_);
                            leanh::lean_inc(v_visitedExpr_5047_);
                            leanh::lean_inc(v_visitedLevel_5046_);
                            leanh::lean_dec(v___x_5045_);
                            v___x_5059_ = leanh::lean_box(0);
                            v_isShared_5060_ = v_isSharedCheck_5066_;
                            state = 17;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v___x_5043_) == 0 {
                            v_a_5067_ = leanh::lean_ctor_get(v___x_5043_, 0);
                            leanh::lean_inc(v_a_5067_);
                            leanh::lean_dec_ref_known(v___x_5043_, 1);
                            v___y_5030_ = v___y_5039_;
                            v_a_5031_ = v_a_5067_;
                            state = 15;
                            continue;
                        } else {
                            leanh::lean_dec(v___y_5039_);
                            leanh::lean_dec_ref_known(v_x_4888_, 2);
                            return v___x_5043_;
                        }
                    }
                } else {
                    v_val_5068_ = leanh::lean_ctor_get(v___x_5042_, 0);
                    leanh::lean_inc(v_val_5068_);
                    leanh::lean_dec_ref_known(v___x_5042_, 1);
                    v___y_5030_ = v___y_5039_;
                    v_a_5031_ = v_val_5068_;
                    state = 15;
                    continue;
                }
            }
            17 => {
                leanh::lean_inc(v_a_5044_);
                leanh::lean_inc(v_a_5028_);
                v___x_5061_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_5046_, v_a_5028_, v_a_5044_);
                if v_isShared_5060_ == 0 {
                    leanh::lean_ctor_set(v___x_5059_, 0, v___x_5061_);
                    v___x_5063_ = v___x_5059_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5065_ = leanh::lean_alloc_ctor(0, 12, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 0, v___x_5061_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 1, v_visitedExpr_5047_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 2, v_levelParams_5048_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 3, v_nextLevelIdx_5049_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 4, v_levelArgs_5050_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 5, v_newLocalDecls_5051_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5065_,
                        6,
                        v_newLocalDeclsForMVars_5052_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 7, v_newLetDecls_5053_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 8, v_nextExprIdx_5054_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 9, v_exprMVarArgs_5055_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 10, v_exprFVarArgs_5056_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 11, v_toProcess_5057_);
                    v___x_5063_ = v_reuseFailAlloc_5065_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_5064_ = lean_st_ref_set(v_a_4889_, v___x_5063_);
                v___y_5030_ = v___y_5039_;
                v_a_5031_ = v_a_5044_;
                state = 15;
                continue;
            }
            19 => {
                v___x_5071_ = l_Lean_Level_hasMVar(v_a_5028_);
                if v___x_5071_ == 0 {
                    v___x_5072_ = l_Lean_Level_hasParam(v_a_5028_);
                    if v___x_5072_ == 0 {
                        leanh::lean_inc(v_a_5028_);
                        v___y_5030_ = v_a_5070_;
                        v_a_5031_ = v_a_5028_;
                        state = 15;
                        continue;
                    } else {
                        v___y_5039_ = v_a_5070_;
                        state = 16;
                        continue;
                    }
                } else {
                    v___y_5039_ = v_a_5070_;
                    state = 16;
                    continue;
                }
            }
            20 => {
                v___x_5074_ = lean_st_ref_get(v_a_4889_);
                v_visitedLevel_5075_ = leanh::lean_ctor_get(v___x_5074_, 0);
                leanh::lean_inc_ref(v_visitedLevel_5075_);
                leanh::lean_dec(v___x_5074_);
                v___x_5076_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_5075_, v_a_5027_);
                leanh::lean_dec_ref(v_visitedLevel_5075_);
                if leanh::lean_obj_tag(v___x_5076_) == 0 {
                    leanh::lean_inc(v_a_5027_);
                    v___x_5077_ =
                        l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_5027_, v_a_4889_);
                    if leanh::lean_obj_tag(v___x_5077_) == 0 {
                        v_a_5078_ = leanh::lean_ctor_get(v___x_5077_, 0);
                        leanh::lean_inc(v_a_5078_);
                        leanh::lean_dec_ref_known(v___x_5077_, 1);
                        v___x_5079_ = lean_st_ref_take(v_a_4889_);
                        v_visitedLevel_5080_ = leanh::lean_ctor_get(v___x_5079_, 0);
                        v_visitedExpr_5081_ = leanh::lean_ctor_get(v___x_5079_, 1);
                        v_levelParams_5082_ = leanh::lean_ctor_get(v___x_5079_, 2);
                        v_nextLevelIdx_5083_ = leanh::lean_ctor_get(v___x_5079_, 3);
                        v_levelArgs_5084_ = leanh::lean_ctor_get(v___x_5079_, 4);
                        v_newLocalDecls_5085_ = leanh::lean_ctor_get(v___x_5079_, 5);
                        v_newLocalDeclsForMVars_5086_ = leanh::lean_ctor_get(v___x_5079_, 6);
                        v_newLetDecls_5087_ = leanh::lean_ctor_get(v___x_5079_, 7);
                        v_nextExprIdx_5088_ = leanh::lean_ctor_get(v___x_5079_, 8);
                        v_exprMVarArgs_5089_ = leanh::lean_ctor_get(v___x_5079_, 9);
                        v_exprFVarArgs_5090_ = leanh::lean_ctor_get(v___x_5079_, 10);
                        v_toProcess_5091_ = leanh::lean_ctor_get(v___x_5079_, 11);
                        v_isSharedCheck_5100_ =
                            (!leanh::lean_is_exclusive(v___x_5079_)) as u8;
                        if v_isSharedCheck_5100_ == 0 {
                            v___x_5093_ = v___x_5079_;
                            v_isShared_5094_ = v_isSharedCheck_5100_;
                            state = 21;
                            continue;
                        } else {
                            leanh::lean_inc(v_toProcess_5091_);
                            leanh::lean_inc(v_exprFVarArgs_5090_);
                            leanh::lean_inc(v_exprMVarArgs_5089_);
                            leanh::lean_inc(v_nextExprIdx_5088_);
                            leanh::lean_inc(v_newLetDecls_5087_);
                            leanh::lean_inc(v_newLocalDeclsForMVars_5086_);
                            leanh::lean_inc(v_newLocalDecls_5085_);
                            leanh::lean_inc(v_levelArgs_5084_);
                            leanh::lean_inc(v_nextLevelIdx_5083_);
                            leanh::lean_inc(v_levelParams_5082_);
                            leanh::lean_inc(v_visitedExpr_5081_);
                            leanh::lean_inc(v_visitedLevel_5080_);
                            leanh::lean_dec(v___x_5079_);
                            v___x_5093_ = leanh::lean_box(0);
                            v_isShared_5094_ = v_isSharedCheck_5100_;
                            state = 21;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v___x_5077_) == 0 {
                            v_a_5101_ = leanh::lean_ctor_get(v___x_5077_, 0);
                            leanh::lean_inc(v_a_5101_);
                            leanh::lean_dec_ref_known(v___x_5077_, 1);
                            v_a_5070_ = v_a_5101_;
                            state = 19;
                            continue;
                        } else {
                            leanh::lean_dec_ref_known(v_x_4888_, 2);
                            return v___x_5077_;
                        }
                    }
                } else {
                    v_val_5102_ = leanh::lean_ctor_get(v___x_5076_, 0);
                    leanh::lean_inc(v_val_5102_);
                    leanh::lean_dec_ref_known(v___x_5076_, 1);
                    v_a_5070_ = v_val_5102_;
                    state = 19;
                    continue;
                }
            }
            21 => {
                leanh::lean_inc(v_a_5078_);
                leanh::lean_inc(v_a_5027_);
                v___x_5095_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_5080_, v_a_5027_, v_a_5078_);
                if v_isShared_5094_ == 0 {
                    leanh::lean_ctor_set(v___x_5093_, 0, v___x_5095_);
                    v___x_5097_ = v___x_5093_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5099_ = leanh::lean_alloc_ctor(0, 12, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5099_, 0, v___x_5095_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5099_, 1, v_visitedExpr_5081_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5099_, 2, v_levelParams_5082_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5099_, 3, v_nextLevelIdx_5083_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5099_, 4, v_levelArgs_5084_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5099_, 5, v_newLocalDecls_5085_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5099_,
                        6,
                        v_newLocalDeclsForMVars_5086_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5099_, 7, v_newLetDecls_5087_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5099_, 8, v_nextExprIdx_5088_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5099_, 9, v_exprMVarArgs_5089_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5099_, 10, v_exprFVarArgs_5090_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5099_, 11, v_toProcess_5091_);
                    v___x_5097_ = v_reuseFailAlloc_5099_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_5098_ = lean_st_ref_set(v_a_4889_, v___x_5097_);
                v_a_5070_ = v_a_5078_;
                state = 19;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Closure_collectLevelAux___redArg___boxed(
    mut v_x_5106_: *mut leanh::LeanObject,
    mut v_a_5107_: *mut leanh::LeanObject,
    mut v_a_5108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5109_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_x_5106_, v_a_5107_);
    leanh::lean_dec(v_a_5107_);
    return v_res_5109_;
}
pub unsafe fn l_Lean_Meta_Closure_collectLevelAux(
    mut v_x_5110_: *mut leanh::LeanObject,
    mut v_a_5111_: u8,
    mut v_a_5112_: *mut leanh::LeanObject,
    mut v_a_5113_: *mut leanh::LeanObject,
    mut v_a_5114_: *mut leanh::LeanObject,
    mut v_a_5115_: *mut leanh::LeanObject,
    mut v_a_5116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5118_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_x_5110_, v_a_5112_);
    return v___x_5118_;
}
pub unsafe fn l_Lean_Meta_Closure_collectLevelAux___boxed(
    mut v_x_5119_: *mut leanh::LeanObject,
    mut v_a_5120_: *mut leanh::LeanObject,
    mut v_a_5121_: *mut leanh::LeanObject,
    mut v_a_5122_: *mut leanh::LeanObject,
    mut v_a_5123_: *mut leanh::LeanObject,
    mut v_a_5124_: *mut leanh::LeanObject,
    mut v_a_5125_: *mut leanh::LeanObject,
    mut v_a_5126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_5127_: u8 = 0;
    let mut v_res_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_5127_ = (leanh::lean_unbox(v_a_5120_) as u8);
    v_res_5128_ = l_Lean_Meta_Closure_collectLevelAux(
        v_x_5119_,
        v_a_boxed_5127_,
        v_a_5121_,
        v_a_5122_,
        v_a_5123_,
        v_a_5124_,
        v_a_5125_,
    );
    leanh::lean_dec(v_a_5125_);
    leanh::lean_dec_ref(v_a_5124_);
    leanh::lean_dec(v_a_5123_);
    leanh::lean_dec_ref(v_a_5122_);
    leanh::lean_dec(v_a_5121_);
    return v_res_5128_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1(
    mut v_00_u03b2_5129_: *mut leanh::LeanObject,
    mut v_m_5130_: *mut leanh::LeanObject,
    mut v_a_5131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5132_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_m_5130_, v_a_5131_);
    return v___x_5132_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___boxed(
    mut v_00_u03b2_5133_: *mut leanh::LeanObject,
    mut v_m_5134_: *mut leanh::LeanObject,
    mut v_a_5135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5136_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1(v_00_u03b2_5133_, v_m_5134_, v_a_5135_);
    leanh::lean_dec(v_a_5135_);
    leanh::lean_dec_ref(v_m_5134_);
    return v_res_5136_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2(
    mut v_00_u03b2_5137_: *mut leanh::LeanObject,
    mut v_m_5138_: *mut leanh::LeanObject,
    mut v_a_5139_: *mut leanh::LeanObject,
    mut v_b_5140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5141_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_m_5138_, v_a_5139_, v_b_5140_);
    return v___x_5141_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1(
    mut v_00_u03b2_5142_: *mut leanh::LeanObject,
    mut v_a_5143_: *mut leanh::LeanObject,
    mut v_x_5144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5145_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(v_a_5143_, v_x_5144_);
    return v___x_5145_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___boxed(
    mut v_00_u03b2_5146_: *mut leanh::LeanObject,
    mut v_a_5147_: *mut leanh::LeanObject,
    mut v_x_5148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5149_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1(v_00_u03b2_5146_, v_a_5147_, v_x_5148_);
    leanh::lean_dec(v_x_5148_);
    leanh::lean_dec(v_a_5147_);
    return v_res_5149_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3(
    mut v_00_u03b2_5150_: *mut leanh::LeanObject,
    mut v_a_5151_: *mut leanh::LeanObject,
    mut v_x_5152_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5153_: u8 = 0;
    v___x_5153_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(v_a_5151_, v_x_5152_);
    return v___x_5153_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___boxed(
    mut v_00_u03b2_5154_: *mut leanh::LeanObject,
    mut v_a_5155_: *mut leanh::LeanObject,
    mut v_x_5156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5157_: u8 = 0;
    let mut v_r_5158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5157_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3(v_00_u03b2_5154_, v_a_5155_, v_x_5156_);
    leanh::lean_dec(v_x_5156_);
    leanh::lean_dec(v_a_5155_);
    v_r_5158_ = leanh::lean_box((v_res_5157_) as usize);
    return v_r_5158_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4(
    mut v_00_u03b2_5159_: *mut leanh::LeanObject,
    mut v_data_5160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5161_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4___redArg(v_data_5160_);
    return v___x_5161_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5(
    mut v_00_u03b2_5162_: *mut leanh::LeanObject,
    mut v_a_5163_: *mut leanh::LeanObject,
    mut v_b_5164_: *mut leanh::LeanObject,
    mut v_x_5165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5166_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5___redArg(v_a_5163_, v_b_5164_, v_x_5165_);
    return v___x_5166_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5(
    mut v_00_u03b2_5167_: *mut leanh::LeanObject,
    mut v_i_5168_: *mut leanh::LeanObject,
    mut v_source_5169_: *mut leanh::LeanObject,
    mut v_target_5170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5171_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5___redArg(v_i_5168_, v_source_5169_, v_target_5170_);
    return v___x_5171_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6(
    mut v_00_u03b2_5172_: *mut leanh::LeanObject,
    mut v_x_5173_: *mut leanh::LeanObject,
    mut v_x_5174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5175_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6___redArg(v_x_5173_, v_x_5174_);
    return v___x_5175_;
}
pub unsafe fn l_Lean_Meta_Closure_collectLevel___redArg(
    mut v_u_5176_: *mut leanh::LeanObject,
    mut v_a_5177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_5181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5187_: u8 = 0;
    let mut v___x_5188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_5189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_5190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_5191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextLevelIdx_5192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelArgs_5193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDecls_5194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDeclsForMVars_5195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLetDecls_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextExprIdx_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprMVarArgs_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprFVarArgs_5199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toProcess_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5203_: u8 = 0;
    let mut v___x_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5212_: u8 = 0;
    let mut v_isSharedCheck_5213_: u8 = 0;
    let mut v_val_5214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5217_: u8 = 0;
    let mut v___x_5219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5221_: u8 = 0;
    let mut v___x_5222_: u8 = 0;
    let mut v___x_5223_: u8 = 0;
    let mut v___x_5224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5222_ = l_Lean_Level_hasMVar(v_u_5176_);
                if v___x_5222_ == 0 {
                    v___x_5223_ = l_Lean_Level_hasParam(v_u_5176_);
                    if v___x_5223_ == 0 {
                        v___x_5224_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5224_, 0, v_u_5176_);
                        return v___x_5224_;
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
                v___x_5180_ = lean_st_ref_get(v_a_5177_);
                v_visitedLevel_5181_ = leanh::lean_ctor_get(v___x_5180_, 0);
                leanh::lean_inc_ref(v_visitedLevel_5181_);
                leanh::lean_dec(v___x_5180_);
                v___x_5182_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_5181_, v_u_5176_);
                leanh::lean_dec_ref(v_visitedLevel_5181_);
                if leanh::lean_obj_tag(v___x_5182_) == 0 {
                    leanh::lean_inc(v_u_5176_);
                    v___x_5183_ =
                        l_Lean_Meta_Closure_collectLevelAux___redArg(v_u_5176_, v_a_5177_);
                    if leanh::lean_obj_tag(v___x_5183_) == 0 {
                        v_a_5184_ = leanh::lean_ctor_get(v___x_5183_, 0);
                        v_isSharedCheck_5213_ =
                            (!leanh::lean_is_exclusive(v___x_5183_)) as u8;
                        if v_isSharedCheck_5213_ == 0 {
                            v___x_5186_ = v___x_5183_;
                            v_isShared_5187_ = v_isSharedCheck_5213_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5184_);
                            leanh::lean_dec(v___x_5183_);
                            v___x_5186_ = leanh::lean_box(0);
                            v_isShared_5187_ = v_isSharedCheck_5213_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_u_5176_);
                        return v___x_5183_;
                    }
                } else {
                    leanh::lean_dec(v_u_5176_);
                    v_val_5214_ = leanh::lean_ctor_get(v___x_5182_, 0);
                    v_isSharedCheck_5221_ = (!leanh::lean_is_exclusive(v___x_5182_)) as u8;
                    if v_isSharedCheck_5221_ == 0 {
                        v___x_5216_ = v___x_5182_;
                        v_isShared_5217_ = v_isSharedCheck_5221_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5214_);
                        leanh::lean_dec(v___x_5182_);
                        v___x_5216_ = leanh::lean_box(0);
                        v_isShared_5217_ = v_isSharedCheck_5221_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5188_ = lean_st_ref_take(v_a_5177_);
                v_visitedLevel_5189_ = leanh::lean_ctor_get(v___x_5188_, 0);
                v_visitedExpr_5190_ = leanh::lean_ctor_get(v___x_5188_, 1);
                v_levelParams_5191_ = leanh::lean_ctor_get(v___x_5188_, 2);
                v_nextLevelIdx_5192_ = leanh::lean_ctor_get(v___x_5188_, 3);
                v_levelArgs_5193_ = leanh::lean_ctor_get(v___x_5188_, 4);
                v_newLocalDecls_5194_ = leanh::lean_ctor_get(v___x_5188_, 5);
                v_newLocalDeclsForMVars_5195_ = leanh::lean_ctor_get(v___x_5188_, 6);
                v_newLetDecls_5196_ = leanh::lean_ctor_get(v___x_5188_, 7);
                v_nextExprIdx_5197_ = leanh::lean_ctor_get(v___x_5188_, 8);
                v_exprMVarArgs_5198_ = leanh::lean_ctor_get(v___x_5188_, 9);
                v_exprFVarArgs_5199_ = leanh::lean_ctor_get(v___x_5188_, 10);
                v_toProcess_5200_ = leanh::lean_ctor_get(v___x_5188_, 11);
                v_isSharedCheck_5212_ = (!leanh::lean_is_exclusive(v___x_5188_)) as u8;
                if v_isSharedCheck_5212_ == 0 {
                    v___x_5202_ = v___x_5188_;
                    v_isShared_5203_ = v_isSharedCheck_5212_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_toProcess_5200_);
                    leanh::lean_inc(v_exprFVarArgs_5199_);
                    leanh::lean_inc(v_exprMVarArgs_5198_);
                    leanh::lean_inc(v_nextExprIdx_5197_);
                    leanh::lean_inc(v_newLetDecls_5196_);
                    leanh::lean_inc(v_newLocalDeclsForMVars_5195_);
                    leanh::lean_inc(v_newLocalDecls_5194_);
                    leanh::lean_inc(v_levelArgs_5193_);
                    leanh::lean_inc(v_nextLevelIdx_5192_);
                    leanh::lean_inc(v_levelParams_5191_);
                    leanh::lean_inc(v_visitedExpr_5190_);
                    leanh::lean_inc(v_visitedLevel_5189_);
                    leanh::lean_dec(v___x_5188_);
                    v___x_5202_ = leanh::lean_box(0);
                    v_isShared_5203_ = v_isSharedCheck_5212_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc(v_a_5184_);
                v___x_5204_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_5189_, v_u_5176_, v_a_5184_);
                if v_isShared_5203_ == 0 {
                    leanh::lean_ctor_set(v___x_5202_, 0, v___x_5204_);
                    v___x_5206_ = v___x_5202_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5211_ = leanh::lean_alloc_ctor(0, 12, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5211_, 0, v___x_5204_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5211_, 1, v_visitedExpr_5190_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5211_, 2, v_levelParams_5191_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5211_, 3, v_nextLevelIdx_5192_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5211_, 4, v_levelArgs_5193_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5211_, 5, v_newLocalDecls_5194_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5211_,
                        6,
                        v_newLocalDeclsForMVars_5195_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5211_, 7, v_newLetDecls_5196_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5211_, 8, v_nextExprIdx_5197_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5211_, 9, v_exprMVarArgs_5198_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5211_, 10, v_exprFVarArgs_5199_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5211_, 11, v_toProcess_5200_);
                    v___x_5206_ = v_reuseFailAlloc_5211_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5207_ = lean_st_ref_set(v_a_5177_, v___x_5206_);
                if v_isShared_5187_ == 0 {
                    v___x_5209_ = v___x_5186_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5210_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5210_, 0, v_a_5184_);
                    v___x_5209_ = v_reuseFailAlloc_5210_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5209_;
            }
            6 => {
                if v_isShared_5217_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5216_, 0);
                    v___x_5219_ = v___x_5216_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5220_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5220_, 0, v_val_5214_);
                    v___x_5219_ = v_reuseFailAlloc_5220_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5219_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Closure_collectLevel___redArg___boxed(
    mut v_u_5225_: *mut leanh::LeanObject,
    mut v_a_5226_: *mut leanh::LeanObject,
    mut v_a_5227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5228_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_5225_, v_a_5226_);
    leanh::lean_dec(v_a_5226_);
    return v_res_5228_;
}
pub unsafe fn l_Lean_Meta_Closure_collectLevel(
    mut v_u_5229_: *mut leanh::LeanObject,
    mut v_a_5230_: u8,
    mut v_a_5231_: *mut leanh::LeanObject,
    mut v_a_5232_: *mut leanh::LeanObject,
    mut v_a_5233_: *mut leanh::LeanObject,
    mut v_a_5234_: *mut leanh::LeanObject,
    mut v_a_5235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5237_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_5229_, v_a_5231_);
    return v___x_5237_;
}
pub unsafe fn l_Lean_Meta_Closure_collectLevel___boxed(
    mut v_u_5238_: *mut leanh::LeanObject,
    mut v_a_5239_: *mut leanh::LeanObject,
    mut v_a_5240_: *mut leanh::LeanObject,
    mut v_a_5241_: *mut leanh::LeanObject,
    mut v_a_5242_: *mut leanh::LeanObject,
    mut v_a_5243_: *mut leanh::LeanObject,
    mut v_a_5244_: *mut leanh::LeanObject,
    mut v_a_5245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_5246_: u8 = 0;
    let mut v_res_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_5246_ = (leanh::lean_unbox(v_a_5239_) as u8);
    v_res_5247_ = l_Lean_Meta_Closure_collectLevel(
        v_u_5238_,
        v_a_boxed_5246_,
        v_a_5240_,
        v_a_5241_,
        v_a_5242_,
        v_a_5243_,
        v_a_5244_,
    );
    leanh::lean_dec(v_a_5244_);
    leanh::lean_dec_ref(v_a_5243_);
    leanh::lean_dec(v_a_5242_);
    leanh::lean_dec_ref(v_a_5241_);
    leanh::lean_dec(v_a_5240_);
    return v_res_5247_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(
    mut v_e_5248_: *mut leanh::LeanObject,
    mut v___y_5249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5251_: u8 = 0;
    let mut v___x_5252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5265_: u8 = 0;
    let mut v___x_5267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5271_: u8 = 0;
    let mut v_unused_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5251_ = l_Lean_Expr_hasMVar(v_e_5248_);
                if v___x_5251_ == 0 {
                    v___x_5252_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5252_, 0, v_e_5248_);
                    return v___x_5252_;
                } else {
                    v___x_5253_ = lean_st_ref_get(v___y_5249_);
                    v_mctx_5254_ = leanh::lean_ctor_get(v___x_5253_, 0);
                    leanh::lean_inc_ref(v_mctx_5254_);
                    leanh::lean_dec(v___x_5253_);
                    v___x_5255_ = l_Lean_instantiateMVarsCore(v_mctx_5254_, v_e_5248_);
                    v_fst_5256_ = leanh::lean_ctor_get(v___x_5255_, 0);
                    leanh::lean_inc(v_fst_5256_);
                    v_snd_5257_ = leanh::lean_ctor_get(v___x_5255_, 1);
                    leanh::lean_inc(v_snd_5257_);
                    leanh::lean_dec_ref(v___x_5255_);
                    v___x_5258_ = lean_st_ref_take(v___y_5249_);
                    v_cache_5259_ = leanh::lean_ctor_get(v___x_5258_, 1);
                    v_zetaDeltaFVarIds_5260_ = leanh::lean_ctor_get(v___x_5258_, 2);
                    v_postponed_5261_ = leanh::lean_ctor_get(v___x_5258_, 3);
                    v_diag_5262_ = leanh::lean_ctor_get(v___x_5258_, 4);
                    v_isSharedCheck_5271_ = (!leanh::lean_is_exclusive(v___x_5258_)) as u8;
                    if v_isSharedCheck_5271_ == 0 {
                        v_unused_5272_ = leanh::lean_ctor_get(v___x_5258_, 0);
                        leanh::lean_dec(v_unused_5272_);
                        v___x_5264_ = v___x_5258_;
                        v_isShared_5265_ = v_isSharedCheck_5271_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_5262_);
                        leanh::lean_inc(v_postponed_5261_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_5260_);
                        leanh::lean_inc(v_cache_5259_);
                        leanh::lean_dec(v___x_5258_);
                        v___x_5264_ = leanh::lean_box(0);
                        v_isShared_5265_ = v_isSharedCheck_5271_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5265_ == 0 {
                    leanh::lean_ctor_set(v___x_5264_, 0, v_snd_5257_);
                    v___x_5267_ = v___x_5264_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5270_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5270_, 0, v_snd_5257_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5270_, 1, v_cache_5259_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5270_,
                        2,
                        v_zetaDeltaFVarIds_5260_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5270_, 3, v_postponed_5261_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5270_, 4, v_diag_5262_);
                    v___x_5267_ = v_reuseFailAlloc_5270_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5268_ = lean_st_ref_set(v___y_5249_, v___x_5267_);
                v___x_5269_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5269_, 0, v_fst_5256_);
                return v___x_5269_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg___boxed(
    mut v_e_5273_: *mut leanh::LeanObject,
    mut v___y_5274_: *mut leanh::LeanObject,
    mut v___y_5275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5276_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(
        v_e_5273_,
        v___y_5274_,
    );
    leanh::lean_dec(v___y_5274_);
    return v_res_5276_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0(
    mut v_e_5277_: *mut leanh::LeanObject,
    mut v___y_5278_: u8,
    mut v___y_5279_: *mut leanh::LeanObject,
    mut v___y_5280_: *mut leanh::LeanObject,
    mut v___y_5281_: *mut leanh::LeanObject,
    mut v___y_5282_: *mut leanh::LeanObject,
    mut v___y_5283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5285_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(
        v_e_5277_,
        v___y_5281_,
    );
    return v___x_5285_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___boxed(
    mut v_e_5286_: *mut leanh::LeanObject,
    mut v___y_5287_: *mut leanh::LeanObject,
    mut v___y_5288_: *mut leanh::LeanObject,
    mut v___y_5289_: *mut leanh::LeanObject,
    mut v___y_5290_: *mut leanh::LeanObject,
    mut v___y_5291_: *mut leanh::LeanObject,
    mut v___y_5292_: *mut leanh::LeanObject,
    mut v___y_5293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2268__boxed_5294_: u8 = 0;
    let mut v_res_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_2268__boxed_5294_ = (leanh::lean_unbox(v___y_5287_) as u8);
    v_res_5295_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0(
        v_e_5286_,
        v___y_2268__boxed_5294_,
        v___y_5288_,
        v___y_5289_,
        v___y_5290_,
        v___y_5291_,
        v___y_5292_,
    );
    leanh::lean_dec(v___y_5292_);
    leanh::lean_dec_ref(v___y_5291_);
    leanh::lean_dec(v___y_5290_);
    leanh::lean_dec_ref(v___y_5289_);
    leanh::lean_dec(v___y_5288_);
    return v_res_5295_;
}
pub unsafe fn l_Lean_Meta_Closure_preprocess(
    mut v_e_5296_: *mut leanh::LeanObject,
    mut v_a_5297_: u8,
    mut v_a_5298_: *mut leanh::LeanObject,
    mut v_a_5299_: *mut leanh::LeanObject,
    mut v_a_5300_: *mut leanh::LeanObject,
    mut v_a_5301_: *mut leanh::LeanObject,
    mut v_a_5302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: u8 = 0;
    let mut v___x_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5310_: u8 = 0;
    let mut v___x_5312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5314_: u8 = 0;
    let mut v_unused_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5319_: u8 = 0;
    let mut v___x_5321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5323_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5304_ =
                    l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(
                        v_e_5296_, v_a_5300_,
                    );
                if v_a_5297_ == 0 {
                    v_a_5305_ = leanh::lean_ctor_get(v___x_5304_, 0);
                    leanh::lean_inc_n(v_a_5305_, 2);
                    leanh::lean_dec_ref(v___x_5304_);
                    v___x_5306_ = 0;
                    v___x_5307_ = l_Lean_Meta_check(
                        v_a_5305_,
                        v___x_5306_,
                        v_a_5299_,
                        v_a_5300_,
                        v_a_5301_,
                        v_a_5302_,
                    );
                    if leanh::lean_obj_tag(v___x_5307_) == 0 {
                        v_isSharedCheck_5314_ =
                            (!leanh::lean_is_exclusive(v___x_5307_)) as u8;
                        if v_isSharedCheck_5314_ == 0 {
                            v_unused_5315_ = leanh::lean_ctor_get(v___x_5307_, 0);
                            leanh::lean_dec(v_unused_5315_);
                            v___x_5309_ = v___x_5307_;
                            v_isShared_5310_ = v_isSharedCheck_5314_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_5307_);
                            v___x_5309_ = leanh::lean_box(0);
                            v_isShared_5310_ = v_isSharedCheck_5314_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_5305_);
                        v_a_5316_ = leanh::lean_ctor_get(v___x_5307_, 0);
                        v_isSharedCheck_5323_ =
                            (!leanh::lean_is_exclusive(v___x_5307_)) as u8;
                        if v_isSharedCheck_5323_ == 0 {
                            v___x_5318_ = v___x_5307_;
                            v_isShared_5319_ = v_isSharedCheck_5323_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5316_);
                            leanh::lean_dec(v___x_5307_);
                            v___x_5318_ = leanh::lean_box(0);
                            v_isShared_5319_ = v_isSharedCheck_5323_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    return v___x_5304_;
                }
            }
            1 => {
                if v_isShared_5310_ == 0 {
                    leanh::lean_ctor_set(v___x_5309_, 0, v_a_5305_);
                    v___x_5312_ = v___x_5309_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5313_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5313_, 0, v_a_5305_);
                    v___x_5312_ = v_reuseFailAlloc_5313_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5312_;
            }
            3 => {
                if v_isShared_5319_ == 0 {
                    v___x_5321_ = v___x_5318_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5322_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5322_, 0, v_a_5316_);
                    v___x_5321_ = v_reuseFailAlloc_5322_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5321_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Closure_preprocess___boxed(
    mut v_e_5324_: *mut leanh::LeanObject,
    mut v_a_5325_: *mut leanh::LeanObject,
    mut v_a_5326_: *mut leanh::LeanObject,
    mut v_a_5327_: *mut leanh::LeanObject,
    mut v_a_5328_: *mut leanh::LeanObject,
    mut v_a_5329_: *mut leanh::LeanObject,
    mut v_a_5330_: *mut leanh::LeanObject,
    mut v_a_5331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_5332_: u8 = 0;
    let mut v_res_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_5332_ = (leanh::lean_unbox(v_a_5325_) as u8);
    v_res_5333_ = l_Lean_Meta_Closure_preprocess(
        v_e_5324_,
        v_a_boxed_5332_,
        v_a_5326_,
        v_a_5327_,
        v_a_5328_,
        v_a_5329_,
        v_a_5330_,
    );
    leanh::lean_dec(v_a_5330_);
    leanh::lean_dec_ref(v_a_5329_);
    leanh::lean_dec(v_a_5328_);
    leanh::lean_dec_ref(v_a_5327_);
    leanh::lean_dec(v_a_5326_);
    return v_res_5333_;
}
pub unsafe fn l_Lean_Meta_Closure_mkNextUserName___redArg(
    mut v_a_5337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_5341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_5342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_5343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextLevelIdx_5344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelArgs_5345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDecls_5346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDeclsForMVars_5347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLetDecls_5348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextExprIdx_5349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprMVarArgs_5350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprFVarArgs_5351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toProcess_5352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5355_: u8 = 0;
    let mut v___x_5356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextExprIdx_5361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5366_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5339_ = lean_st_ref_get(v_a_5337_);
                v___x_5340_ = lean_st_ref_take(v_a_5337_);
                v_visitedLevel_5341_ = leanh::lean_ctor_get(v___x_5340_, 0);
                v_visitedExpr_5342_ = leanh::lean_ctor_get(v___x_5340_, 1);
                v_levelParams_5343_ = leanh::lean_ctor_get(v___x_5340_, 2);
                v_nextLevelIdx_5344_ = leanh::lean_ctor_get(v___x_5340_, 3);
                v_levelArgs_5345_ = leanh::lean_ctor_get(v___x_5340_, 4);
                v_newLocalDecls_5346_ = leanh::lean_ctor_get(v___x_5340_, 5);
                v_newLocalDeclsForMVars_5347_ = leanh::lean_ctor_get(v___x_5340_, 6);
                v_newLetDecls_5348_ = leanh::lean_ctor_get(v___x_5340_, 7);
                v_nextExprIdx_5349_ = leanh::lean_ctor_get(v___x_5340_, 8);
                v_exprMVarArgs_5350_ = leanh::lean_ctor_get(v___x_5340_, 9);
                v_exprFVarArgs_5351_ = leanh::lean_ctor_get(v___x_5340_, 10);
                v_toProcess_5352_ = leanh::lean_ctor_get(v___x_5340_, 11);
                v_isSharedCheck_5366_ = (!leanh::lean_is_exclusive(v___x_5340_)) as u8;
                if v_isSharedCheck_5366_ == 0 {
                    v___x_5354_ = v___x_5340_;
                    v_isShared_5355_ = v_isSharedCheck_5366_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toProcess_5352_);
                    leanh::lean_inc(v_exprFVarArgs_5351_);
                    leanh::lean_inc(v_exprMVarArgs_5350_);
                    leanh::lean_inc(v_nextExprIdx_5349_);
                    leanh::lean_inc(v_newLetDecls_5348_);
                    leanh::lean_inc(v_newLocalDeclsForMVars_5347_);
                    leanh::lean_inc(v_newLocalDecls_5346_);
                    leanh::lean_inc(v_levelArgs_5345_);
                    leanh::lean_inc(v_nextLevelIdx_5344_);
                    leanh::lean_inc(v_levelParams_5343_);
                    leanh::lean_inc(v_visitedExpr_5342_);
                    leanh::lean_inc(v_visitedLevel_5341_);
                    leanh::lean_dec(v___x_5340_);
                    v___x_5354_ = leanh::lean_box(0);
                    v_isShared_5355_ = v_isSharedCheck_5366_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5356_ = leanh::lean_unsigned_to_nat(1);
                v___x_5357_ = lean_nat_add(v_nextExprIdx_5349_, v___x_5356_);
                leanh::lean_dec(v_nextExprIdx_5349_);
                if v_isShared_5355_ == 0 {
                    leanh::lean_ctor_set(v___x_5354_, 8, v___x_5357_);
                    v___x_5359_ = v___x_5354_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5365_ = leanh::lean_alloc_ctor(0, 12, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5365_, 0, v_visitedLevel_5341_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5365_, 1, v_visitedExpr_5342_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5365_, 2, v_levelParams_5343_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5365_, 3, v_nextLevelIdx_5344_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5365_, 4, v_levelArgs_5345_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5365_, 5, v_newLocalDecls_5346_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5365_,
                        6,
                        v_newLocalDeclsForMVars_5347_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5365_, 7, v_newLetDecls_5348_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5365_, 8, v___x_5357_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5365_, 9, v_exprMVarArgs_5350_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5365_, 10, v_exprFVarArgs_5351_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5365_, 11, v_toProcess_5352_);
                    v___x_5359_ = v_reuseFailAlloc_5365_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5360_ = lean_st_ref_set(v_a_5337_, v___x_5359_);
                v_nextExprIdx_5361_ = leanh::lean_ctor_get(v___x_5339_, 8);
                leanh::lean_inc(v_nextExprIdx_5361_);
                leanh::lean_dec(v___x_5339_);
                v___x_5362_ = l_Lean_Meta_Closure_mkNextUserName___redArg___closed__1;
                v___x_5363_ = lean_name_append_index_after(v___x_5362_, v_nextExprIdx_5361_);
                v___x_5364_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5364_, 0, v___x_5363_);
                return v___x_5364_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Closure_mkNextUserName___redArg___boxed(
    mut v_a_5367_: *mut leanh::LeanObject,
    mut v_a_5368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5369_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_5367_);
    leanh::lean_dec(v_a_5367_);
    return v_res_5369_;
}
pub unsafe fn l_Lean_Meta_Closure_mkNextUserName(
    mut v_a_5370_: u8,
    mut v_a_5371_: *mut leanh::LeanObject,
    mut v_a_5372_: *mut leanh::LeanObject,
    mut v_a_5373_: *mut leanh::LeanObject,
    mut v_a_5374_: *mut leanh::LeanObject,
    mut v_a_5375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5377_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_5371_);
    return v___x_5377_;
}
pub unsafe fn l_Lean_Meta_Closure_mkNextUserName___boxed(
    mut v_a_5378_: *mut leanh::LeanObject,
    mut v_a_5379_: *mut leanh::LeanObject,
    mut v_a_5380_: *mut leanh::LeanObject,
    mut v_a_5381_: *mut leanh::LeanObject,
    mut v_a_5382_: *mut leanh::LeanObject,
    mut v_a_5383_: *mut leanh::LeanObject,
    mut v_a_5384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_5385_: u8 = 0;
    let mut v_res_5386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_5385_ = (leanh::lean_unbox(v_a_5378_) as u8);
    v_res_5386_ = l_Lean_Meta_Closure_mkNextUserName(
        v_a_boxed_5385_,
        v_a_5379_,
        v_a_5380_,
        v_a_5381_,
        v_a_5382_,
        v_a_5383_,
    );
    leanh::lean_dec(v_a_5383_);
    leanh::lean_dec_ref(v_a_5382_);
    leanh::lean_dec(v_a_5381_);
    leanh::lean_dec_ref(v_a_5380_);
    leanh::lean_dec(v_a_5379_);
    return v_res_5386_;
}
pub unsafe fn l_Lean_Meta_Closure_pushToProcess___redArg(
    mut v_elem_5387_: *mut leanh::LeanObject,
    mut v_a_5388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_5391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_5392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_5393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextLevelIdx_5394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelArgs_5395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDecls_5396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDeclsForMVars_5397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLetDecls_5398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextExprIdx_5399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprMVarArgs_5400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprFVarArgs_5401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toProcess_5402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5405_: u8 = 0;
    let mut v___x_5406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5413_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5390_ = lean_st_ref_take(v_a_5388_);
                v_visitedLevel_5391_ = leanh::lean_ctor_get(v___x_5390_, 0);
                v_visitedExpr_5392_ = leanh::lean_ctor_get(v___x_5390_, 1);
                v_levelParams_5393_ = leanh::lean_ctor_get(v___x_5390_, 2);
                v_nextLevelIdx_5394_ = leanh::lean_ctor_get(v___x_5390_, 3);
                v_levelArgs_5395_ = leanh::lean_ctor_get(v___x_5390_, 4);
                v_newLocalDecls_5396_ = leanh::lean_ctor_get(v___x_5390_, 5);
                v_newLocalDeclsForMVars_5397_ = leanh::lean_ctor_get(v___x_5390_, 6);
                v_newLetDecls_5398_ = leanh::lean_ctor_get(v___x_5390_, 7);
                v_nextExprIdx_5399_ = leanh::lean_ctor_get(v___x_5390_, 8);
                v_exprMVarArgs_5400_ = leanh::lean_ctor_get(v___x_5390_, 9);
                v_exprFVarArgs_5401_ = leanh::lean_ctor_get(v___x_5390_, 10);
                v_toProcess_5402_ = leanh::lean_ctor_get(v___x_5390_, 11);
                v_isSharedCheck_5413_ = (!leanh::lean_is_exclusive(v___x_5390_)) as u8;
                if v_isSharedCheck_5413_ == 0 {
                    v___x_5404_ = v___x_5390_;
                    v_isShared_5405_ = v_isSharedCheck_5413_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toProcess_5402_);
                    leanh::lean_inc(v_exprFVarArgs_5401_);
                    leanh::lean_inc(v_exprMVarArgs_5400_);
                    leanh::lean_inc(v_nextExprIdx_5399_);
                    leanh::lean_inc(v_newLetDecls_5398_);
                    leanh::lean_inc(v_newLocalDeclsForMVars_5397_);
                    leanh::lean_inc(v_newLocalDecls_5396_);
                    leanh::lean_inc(v_levelArgs_5395_);
                    leanh::lean_inc(v_nextLevelIdx_5394_);
                    leanh::lean_inc(v_levelParams_5393_);
                    leanh::lean_inc(v_visitedExpr_5392_);
                    leanh::lean_inc(v_visitedLevel_5391_);
                    leanh::lean_dec(v___x_5390_);
                    v___x_5404_ = leanh::lean_box(0);
                    v_isShared_5405_ = v_isSharedCheck_5413_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5406_ = lean_array_push(v_toProcess_5402_, v_elem_5387_);
                if v_isShared_5405_ == 0 {
                    leanh::lean_ctor_set(v___x_5404_, 11, v___x_5406_);
                    v___x_5408_ = v___x_5404_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5412_ = leanh::lean_alloc_ctor(0, 12, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5412_, 0, v_visitedLevel_5391_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5412_, 1, v_visitedExpr_5392_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5412_, 2, v_levelParams_5393_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5412_, 3, v_nextLevelIdx_5394_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5412_, 4, v_levelArgs_5395_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5412_, 5, v_newLocalDecls_5396_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5412_,
                        6,
                        v_newLocalDeclsForMVars_5397_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5412_, 7, v_newLetDecls_5398_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5412_, 8, v_nextExprIdx_5399_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5412_, 9, v_exprMVarArgs_5400_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5412_, 10, v_exprFVarArgs_5401_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5412_, 11, v___x_5406_);
                    v___x_5408_ = v_reuseFailAlloc_5412_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5409_ = lean_st_ref_set(v_a_5388_, v___x_5408_);
                v___x_5410_ = leanh::lean_box(0);
                v___x_5411_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5411_, 0, v___x_5410_);
                return v___x_5411_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Closure_pushToProcess___redArg___boxed(
    mut v_elem_5414_: *mut leanh::LeanObject,
    mut v_a_5415_: *mut leanh::LeanObject,
    mut v_a_5416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5417_ = l_Lean_Meta_Closure_pushToProcess___redArg(v_elem_5414_, v_a_5415_);
    leanh::lean_dec(v_a_5415_);
    return v_res_5417_;
}
pub unsafe fn l_Lean_Meta_Closure_pushToProcess(
    mut v_elem_5418_: *mut leanh::LeanObject,
    mut v_a_5419_: u8,
    mut v_a_5420_: *mut leanh::LeanObject,
    mut v_a_5421_: *mut leanh::LeanObject,
    mut v_a_5422_: *mut leanh::LeanObject,
    mut v_a_5423_: *mut leanh::LeanObject,
    mut v_a_5424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5426_ = l_Lean_Meta_Closure_pushToProcess___redArg(v_elem_5418_, v_a_5420_);
    return v___x_5426_;
}
pub unsafe fn l_Lean_Meta_Closure_pushToProcess___boxed(
    mut v_elem_5427_: *mut leanh::LeanObject,
    mut v_a_5428_: *mut leanh::LeanObject,
    mut v_a_5429_: *mut leanh::LeanObject,
    mut v_a_5430_: *mut leanh::LeanObject,
    mut v_a_5431_: *mut leanh::LeanObject,
    mut v_a_5432_: *mut leanh::LeanObject,
    mut v_a_5433_: *mut leanh::LeanObject,
    mut v_a_5434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_5435_: u8 = 0;
    let mut v_res_5436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_5435_ = (leanh::lean_unbox(v_a_5428_) as u8);
    v_res_5436_ = l_Lean_Meta_Closure_pushToProcess(
        v_elem_5427_,
        v_a_boxed_5435_,
        v_a_5429_,
        v_a_5430_,
        v_a_5431_,
        v_a_5432_,
        v_a_5433_,
    );
    leanh::lean_dec(v_a_5433_);
    leanh::lean_dec_ref(v_a_5432_);
    leanh::lean_dec(v_a_5431_);
    leanh::lean_dec_ref(v_a_5430_);
    leanh::lean_dec(v_a_5429_);
    return v_res_5436_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(
    mut v_mvarId_5437_: *mut leanh::LeanObject,
    mut v___y_5438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5440_ = lean_st_ref_get(v___y_5438_);
    v_mctx_5441_ = leanh::lean_ctor_get(v___x_5440_, 0);
    leanh::lean_inc_ref(v_mctx_5441_);
    leanh::lean_dec(v___x_5440_);
    v___x_5442_ =
        l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_5441_, v_mvarId_5437_);
    leanh::lean_dec_ref(v_mctx_5441_);
    v___x_5443_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5443_, 0, v___x_5442_);
    return v___x_5443_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg___boxed(
    mut v_mvarId_5444_: *mut leanh::LeanObject,
    mut v___y_5445_: *mut leanh::LeanObject,
    mut v___y_5446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5447_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_5444_, v___y_5445_);
    leanh::lean_dec(v___y_5445_);
    leanh::lean_dec(v_mvarId_5444_);
    return v_res_5447_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4(
    mut v_mvarId_5448_: *mut leanh::LeanObject,
    mut v___y_5449_: u8,
    mut v___y_5450_: *mut leanh::LeanObject,
    mut v___y_5451_: *mut leanh::LeanObject,
    mut v___y_5452_: *mut leanh::LeanObject,
    mut v___y_5453_: *mut leanh::LeanObject,
    mut v___y_5454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5456_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_5448_, v___y_5452_);
    return v___x_5456_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___boxed(
    mut v_mvarId_5457_: *mut leanh::LeanObject,
    mut v___y_5458_: *mut leanh::LeanObject,
    mut v___y_5459_: *mut leanh::LeanObject,
    mut v___y_5460_: *mut leanh::LeanObject,
    mut v___y_5461_: *mut leanh::LeanObject,
    mut v___y_5462_: *mut leanh::LeanObject,
    mut v___y_5463_: *mut leanh::LeanObject,
    mut v___y_5464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_17871__boxed_5465_: u8 = 0;
    let mut v_res_5466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_17871__boxed_5465_ = (leanh::lean_unbox(v___y_5458_) as u8);
    v_res_5466_ =
        l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4(
            v_mvarId_5457_,
            v___y_17871__boxed_5465_,
            v___y_5459_,
            v___y_5460_,
            v___y_5461_,
            v___y_5462_,
            v___y_5463_,
        );
    leanh::lean_dec(v___y_5463_);
    leanh::lean_dec_ref(v___y_5462_);
    leanh::lean_dec(v___y_5461_);
    leanh::lean_dec_ref(v___y_5460_);
    leanh::lean_dec(v___y_5459_);
    leanh::lean_dec(v_mvarId_5457_);
    return v_res_5466_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0(
    mut v_k_5467_: *mut leanh::LeanObject,
    mut v___y_5468_: u8,
    mut v___y_5469_: *mut leanh::LeanObject,
    mut v_b_5470_: *mut leanh::LeanObject,
    mut v_c_5471_: *mut leanh::LeanObject,
    mut v___y_5472_: *mut leanh::LeanObject,
    mut v___y_5473_: *mut leanh::LeanObject,
    mut v___y_5474_: *mut leanh::LeanObject,
    mut v___y_5475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5477_ = leanh::lean_box((v___y_5468_) as usize);
    leanh::lean_inc(v___y_5475_);
    leanh::lean_inc_ref(v___y_5474_);
    leanh::lean_inc(v___y_5473_);
    leanh::lean_inc_ref(v___y_5472_);
    leanh::lean_inc(v___y_5469_);
    v___x_5478_ = leanh::lean_apply_9(
        v_k_5467_,
        v_b_5470_,
        v_c_5471_,
        v___x_5477_,
        v___y_5469_,
        v___y_5472_,
        v___y_5473_,
        v___y_5474_,
        v___y_5475_,
        leanh::lean_box(0),
    );
    return v___x_5478_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0___boxed(
    mut v_k_5479_: *mut leanh::LeanObject,
    mut v___y_5480_: *mut leanh::LeanObject,
    mut v___y_5481_: *mut leanh::LeanObject,
    mut v_b_5482_: *mut leanh::LeanObject,
    mut v_c_5483_: *mut leanh::LeanObject,
    mut v___y_5484_: *mut leanh::LeanObject,
    mut v___y_5485_: *mut leanh::LeanObject,
    mut v___y_5486_: *mut leanh::LeanObject,
    mut v___y_5487_: *mut leanh::LeanObject,
    mut v___y_5488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_17894__boxed_5489_: u8 = 0;
    let mut v_res_5490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_17894__boxed_5489_ = (leanh::lean_unbox(v___y_5480_) as u8);
    v_res_5490_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0(v_k_5479_, v___y_17894__boxed_5489_, v___y_5481_, v_b_5482_, v_c_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_);
    leanh::lean_dec(v___y_5487_);
    leanh::lean_dec_ref(v___y_5486_);
    leanh::lean_dec(v___y_5485_);
    leanh::lean_dec_ref(v___y_5484_);
    leanh::lean_dec(v___y_5481_);
    return v_res_5490_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(
    mut v_type_5491_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_5492_: *mut leanh::LeanObject,
    mut v_k_5493_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_5494_: u8,
    mut v_whnfType_5495_: u8,
    mut v___y_5496_: u8,
    mut v___y_5497_: *mut leanh::LeanObject,
    mut v___y_5498_: *mut leanh::LeanObject,
    mut v___y_5499_: *mut leanh::LeanObject,
    mut v___y_5500_: *mut leanh::LeanObject,
    mut v___y_5501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5509_: u8 = 0;
    let mut v___x_5511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5513_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5503_ = leanh::lean_box((v___y_5496_) as usize);
                leanh::lean_inc(v___y_5497_);
                v___f_5504_ = leanh::lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                leanh::lean_closure_set(v___f_5504_, 0, v_k_5493_);
                leanh::lean_closure_set(v___f_5504_, 1, v___x_5503_);
                leanh::lean_closure_set(v___f_5504_, 2, v___y_5497_);
                v___x_5505_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    leanh::lean_box(0),
                    v_type_5491_,
                    v_maxFVars_x3f_5492_,
                    v___f_5504_,
                    v_cleanupAnnotations_5494_,
                    v_whnfType_5495_,
                    v___y_5498_,
                    v___y_5499_,
                    v___y_5500_,
                    v___y_5501_,
                );
                if leanh::lean_obj_tag(v___x_5505_) == 0 {
                    return v___x_5505_;
                } else {
                    v_a_5506_ = leanh::lean_ctor_get(v___x_5505_, 0);
                    v_isSharedCheck_5513_ = (!leanh::lean_is_exclusive(v___x_5505_)) as u8;
                    if v_isSharedCheck_5513_ == 0 {
                        v___x_5508_ = v___x_5505_;
                        v_isShared_5509_ = v_isSharedCheck_5513_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5506_);
                        leanh::lean_dec(v___x_5505_);
                        v___x_5508_ = leanh::lean_box(0);
                        v_isShared_5509_ = v_isSharedCheck_5513_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5509_ == 0 {
                    v___x_5511_ = v___x_5508_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5512_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5512_, 0, v_a_5506_);
                    v___x_5511_ = v_reuseFailAlloc_5512_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5511_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___boxed(
    mut v_type_5514_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_5515_: *mut leanh::LeanObject,
    mut v_k_5516_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_5517_: *mut leanh::LeanObject,
    mut v_whnfType_5518_: *mut leanh::LeanObject,
    mut v___y_5519_: *mut leanh::LeanObject,
    mut v___y_5520_: *mut leanh::LeanObject,
    mut v___y_5521_: *mut leanh::LeanObject,
    mut v___y_5522_: *mut leanh::LeanObject,
    mut v___y_5523_: *mut leanh::LeanObject,
    mut v___y_5524_: *mut leanh::LeanObject,
    mut v___y_5525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_5526_: u8 = 0;
    let mut v_whnfType_boxed_5527_: u8 = 0;
    let mut v___y_17919__boxed_5528_: u8 = 0;
    let mut v_res_5529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5526_ = (leanh::lean_unbox(v_cleanupAnnotations_5517_) as u8);
    v_whnfType_boxed_5527_ = (leanh::lean_unbox(v_whnfType_5518_) as u8);
    v___y_17919__boxed_5528_ = (leanh::lean_unbox(v___y_5519_) as u8);
    v_res_5529_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_5514_, v_maxFVars_x3f_5515_, v_k_5516_, v_cleanupAnnotations_boxed_5526_, v_whnfType_boxed_5527_, v___y_17919__boxed_5528_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_, v___y_5524_);
    leanh::lean_dec(v___y_5524_);
    leanh::lean_dec_ref(v___y_5523_);
    leanh::lean_dec(v___y_5522_);
    leanh::lean_dec_ref(v___y_5521_);
    leanh::lean_dec(v___y_5520_);
    return v_res_5529_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5(
    mut v_00_u03b1_5530_: *mut leanh::LeanObject,
    mut v_type_5531_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_5532_: *mut leanh::LeanObject,
    mut v_k_5533_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_5534_: u8,
    mut v_whnfType_5535_: u8,
    mut v___y_5536_: u8,
    mut v___y_5537_: *mut leanh::LeanObject,
    mut v___y_5538_: *mut leanh::LeanObject,
    mut v___y_5539_: *mut leanh::LeanObject,
    mut v___y_5540_: *mut leanh::LeanObject,
    mut v___y_5541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5543_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_5531_, v_maxFVars_x3f_5532_, v_k_5533_, v_cleanupAnnotations_5534_, v_whnfType_5535_, v___y_5536_, v___y_5537_, v___y_5538_, v___y_5539_, v___y_5540_, v___y_5541_);
    return v___x_5543_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___boxed(
    mut v_00_u03b1_5544_: *mut leanh::LeanObject,
    mut v_type_5545_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_5546_: *mut leanh::LeanObject,
    mut v_k_5547_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_5548_: *mut leanh::LeanObject,
    mut v_whnfType_5549_: *mut leanh::LeanObject,
    mut v___y_5550_: *mut leanh::LeanObject,
    mut v___y_5551_: *mut leanh::LeanObject,
    mut v___y_5552_: *mut leanh::LeanObject,
    mut v___y_5553_: *mut leanh::LeanObject,
    mut v___y_5554_: *mut leanh::LeanObject,
    mut v___y_5555_: *mut leanh::LeanObject,
    mut v___y_5556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_5557_: u8 = 0;
    let mut v_whnfType_boxed_5558_: u8 = 0;
    let mut v___y_17963__boxed_5559_: u8 = 0;
    let mut v_res_5560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5557_ = (leanh::lean_unbox(v_cleanupAnnotations_5548_) as u8);
    v_whnfType_boxed_5558_ = (leanh::lean_unbox(v_whnfType_5549_) as u8);
    v___y_17963__boxed_5559_ = (leanh::lean_unbox(v___y_5550_) as u8);
    v_res_5560_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5(
            v_00_u03b1_5544_,
            v_type_5545_,
            v_maxFVars_x3f_5546_,
            v_k_5547_,
            v_cleanupAnnotations_boxed_5557_,
            v_whnfType_boxed_5558_,
            v___y_17963__boxed_5559_,
            v___y_5551_,
            v___y_5552_,
            v___y_5553_,
            v___y_5554_,
            v___y_5555_,
        );
    leanh::lean_dec(v___y_5555_);
    leanh::lean_dec_ref(v___y_5554_);
    leanh::lean_dec(v___y_5553_);
    leanh::lean_dec_ref(v___y_5552_);
    leanh::lean_dec(v___y_5551_);
    return v_res_5560_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(
    mut v_a_5561_: *mut leanh::LeanObject,
    mut v_x_5562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: u8 = 0;
    let mut v___x_5569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5562_) == 0 {
                    v___x_5563_ = leanh::lean_box(0);
                    return v___x_5563_;
                } else {
                    v_key_5564_ = leanh::lean_ctor_get(v_x_5562_, 0);
                    v_value_5565_ = leanh::lean_ctor_get(v_x_5562_, 1);
                    v_tail_5566_ = leanh::lean_ctor_get(v_x_5562_, 2);
                    v___x_5567_ = l_Lean_ExprStructEq_beq(v_key_5564_, v_a_5561_);
                    if v___x_5567_ == 0 {
                        v_x_5562_ = v_tail_5566_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_5565_);
                        v___x_5569_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5569_, 0, v_value_5565_);
                        return v___x_5569_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg___boxed(
    mut v_a_5570_: *mut leanh::LeanObject,
    mut v_x_5571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5572_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_5570_, v_x_5571_);
    leanh::lean_dec(v_x_5571_);
    leanh::lean_dec_ref(v_a_5570_);
    return v_res_5572_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(
    mut v_m_5573_: *mut leanh::LeanObject,
    mut v_a_5574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_5575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: u64 = 0;
    let mut v___x_5578_: u64 = 0;
    let mut v___x_5579_: u64 = 0;
    let mut v_fold_5580_: u64 = 0;
    let mut v___x_5581_: u64 = 0;
    let mut v___x_5582_: u64 = 0;
    let mut v___x_5583_: u64 = 0;
    let mut v___x_5584_: usize = 0;
    let mut v___x_5585_: usize = 0;
    let mut v___x_5586_: usize = 0;
    let mut v___x_5587_: usize = 0;
    let mut v___x_5588_: usize = 0;
    let mut v___x_5589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_5575_ = leanh::lean_ctor_get(v_m_5573_, 1);
    v___x_5576_ = lean_array_get_size(v_buckets_5575_);
    v___x_5577_ = l_Lean_ExprStructEq_hash(v_a_5574_);
    v___x_5578_ = 32u64;
    v___x_5579_ = lean_uint64_shift_right(v___x_5577_, v___x_5578_);
    v_fold_5580_ = lean_uint64_xor(v___x_5577_, v___x_5579_);
    v___x_5581_ = 16u64;
    v___x_5582_ = lean_uint64_shift_right(v_fold_5580_, v___x_5581_);
    v___x_5583_ = lean_uint64_xor(v_fold_5580_, v___x_5582_);
    v___x_5584_ = lean_uint64_to_usize(v___x_5583_);
    v___x_5585_ = lean_usize_of_nat(v___x_5576_);
    v___x_5586_ = 1usize;
    v___x_5587_ = lean_usize_sub(v___x_5585_, v___x_5586_);
    v___x_5588_ = lean_usize_land(v___x_5584_, v___x_5587_);
    v___x_5589_ = lean_array_uget_borrowed(v_buckets_5575_, v___x_5588_);
    v___x_5590_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_5574_, v___x_5589_);
    return v___x_5590_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg___boxed(
    mut v_m_5591_: *mut leanh::LeanObject,
    mut v_a_5592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5593_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_m_5591_, v_a_5592_);
    leanh::lean_dec_ref(v_a_5592_);
    leanh::lean_dec_ref(v_m_5591_);
    return v_res_5593_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(
    mut v_x_5594_: *mut leanh::LeanObject,
    mut v_x_5595_: *mut leanh::LeanObject,
    mut v___y_5596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5604_: u8 = 0;
    let mut v___x_5605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5614_: u8 = 0;
    let mut v___x_5616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5618_: u8 = 0;
    let mut v_isSharedCheck_5619_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5594_) == 0 {
                    v___x_5598_ = l_List_reverse___redArg(v_x_5595_);
                    v___x_5599_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5599_, 0, v___x_5598_);
                    return v___x_5599_;
                } else {
                    v_head_5600_ = leanh::lean_ctor_get(v_x_5594_, 0);
                    v_tail_5601_ = leanh::lean_ctor_get(v_x_5594_, 1);
                    v_isSharedCheck_5619_ = (!leanh::lean_is_exclusive(v_x_5594_)) as u8;
                    if v_isSharedCheck_5619_ == 0 {
                        v___x_5603_ = v_x_5594_;
                        v_isShared_5604_ = v_isSharedCheck_5619_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5601_);
                        leanh::lean_inc(v_head_5600_);
                        leanh::lean_dec(v_x_5594_);
                        v___x_5603_ = leanh::lean_box(0);
                        v_isShared_5604_ = v_isSharedCheck_5619_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5605_ = l_Lean_Meta_Closure_collectLevel___redArg(v_head_5600_, v___y_5596_);
                if leanh::lean_obj_tag(v___x_5605_) == 0 {
                    v_a_5606_ = leanh::lean_ctor_get(v___x_5605_, 0);
                    leanh::lean_inc(v_a_5606_);
                    leanh::lean_dec_ref_known(v___x_5605_, 1);
                    if v_isShared_5604_ == 0 {
                        leanh::lean_ctor_set(v___x_5603_, 1, v_x_5595_);
                        leanh::lean_ctor_set(v___x_5603_, 0, v_a_5606_);
                        v___x_5608_ = v___x_5603_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5610_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5610_, 0, v_a_5606_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5610_, 1, v_x_5595_);
                        v___x_5608_ = v_reuseFailAlloc_5610_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5603_);
                    leanh::lean_dec(v_tail_5601_);
                    leanh::lean_dec(v_x_5595_);
                    v_a_5611_ = leanh::lean_ctor_get(v___x_5605_, 0);
                    v_isSharedCheck_5618_ = (!leanh::lean_is_exclusive(v___x_5605_)) as u8;
                    if v_isSharedCheck_5618_ == 0 {
                        v___x_5613_ = v___x_5605_;
                        v_isShared_5614_ = v_isSharedCheck_5618_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5611_);
                        leanh::lean_dec(v___x_5605_);
                        v___x_5613_ = leanh::lean_box(0);
                        v_isShared_5614_ = v_isSharedCheck_5618_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_5594_ = v_tail_5601_;
                v_x_5595_ = v___x_5608_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_5614_ == 0 {
                    v___x_5616_ = v___x_5613_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5617_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5617_, 0, v_a_5611_);
                    v___x_5616_ = v_reuseFailAlloc_5617_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5616_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg___boxed(
    mut v_x_5620_: *mut leanh::LeanObject,
    mut v_x_5621_: *mut leanh::LeanObject,
    mut v___y_5622_: *mut leanh::LeanObject,
    mut v___y_5623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5624_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(
        v_x_5620_,
        v_x_5621_,
        v___y_5622_,
    );
    leanh::lean_dec(v___y_5622_);
    return v_res_5624_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(
    mut v___y_5625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_5629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_5630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5633_: u8 = 0;
    let mut v___x_5634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5645_: u8 = 0;
    let mut v_r_5646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5657_: u8 = 0;
    let mut v_unused_5658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5659_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5627_ = lean_st_ref_get(v___y_5625_);
                v_ngen_5628_ = leanh::lean_ctor_get(v___x_5627_, 2);
                leanh::lean_inc_ref(v_ngen_5628_);
                leanh::lean_dec(v___x_5627_);
                v_namePrefix_5629_ = leanh::lean_ctor_get(v_ngen_5628_, 0);
                v_idx_5630_ = leanh::lean_ctor_get(v_ngen_5628_, 1);
                v_isSharedCheck_5659_ = (!leanh::lean_is_exclusive(v_ngen_5628_)) as u8;
                if v_isSharedCheck_5659_ == 0 {
                    v___x_5632_ = v_ngen_5628_;
                    v_isShared_5633_ = v_isSharedCheck_5659_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_idx_5630_);
                    leanh::lean_inc(v_namePrefix_5629_);
                    leanh::lean_dec(v_ngen_5628_);
                    v___x_5632_ = leanh::lean_box(0);
                    v_isShared_5633_ = v_isSharedCheck_5659_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5634_ = lean_st_ref_take(v___y_5625_);
                v_env_5635_ = leanh::lean_ctor_get(v___x_5634_, 0);
                v_nextMacroScope_5636_ = leanh::lean_ctor_get(v___x_5634_, 1);
                v_auxDeclNGen_5637_ = leanh::lean_ctor_get(v___x_5634_, 3);
                v_traceState_5638_ = leanh::lean_ctor_get(v___x_5634_, 4);
                v_cache_5639_ = leanh::lean_ctor_get(v___x_5634_, 5);
                v_messages_5640_ = leanh::lean_ctor_get(v___x_5634_, 6);
                v_infoState_5641_ = leanh::lean_ctor_get(v___x_5634_, 7);
                v_snapshotTasks_5642_ = leanh::lean_ctor_get(v___x_5634_, 8);
                v_isSharedCheck_5657_ = (!leanh::lean_is_exclusive(v___x_5634_)) as u8;
                if v_isSharedCheck_5657_ == 0 {
                    v_unused_5658_ = leanh::lean_ctor_get(v___x_5634_, 2);
                    leanh::lean_dec(v_unused_5658_);
                    v___x_5644_ = v___x_5634_;
                    v_isShared_5645_ = v_isSharedCheck_5657_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_5642_);
                    leanh::lean_inc(v_infoState_5641_);
                    leanh::lean_inc(v_messages_5640_);
                    leanh::lean_inc(v_cache_5639_);
                    leanh::lean_inc(v_traceState_5638_);
                    leanh::lean_inc(v_auxDeclNGen_5637_);
                    leanh::lean_inc(v_nextMacroScope_5636_);
                    leanh::lean_inc(v_env_5635_);
                    leanh::lean_dec(v___x_5634_);
                    v___x_5644_ = leanh::lean_box(0);
                    v_isShared_5645_ = v_isSharedCheck_5657_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_idx_5630_);
                leanh::lean_inc(v_namePrefix_5629_);
                v_r_5646_ = l_Lean_Name_num___override(v_namePrefix_5629_, v_idx_5630_);
                v___x_5647_ = leanh::lean_unsigned_to_nat(1);
                v___x_5648_ = lean_nat_add(v_idx_5630_, v___x_5647_);
                leanh::lean_dec(v_idx_5630_);
                if v_isShared_5633_ == 0 {
                    leanh::lean_ctor_set(v___x_5632_, 1, v___x_5648_);
                    v___x_5650_ = v___x_5632_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5656_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5656_, 0, v_namePrefix_5629_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5656_, 1, v___x_5648_);
                    v___x_5650_ = v_reuseFailAlloc_5656_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5645_ == 0 {
                    leanh::lean_ctor_set(v___x_5644_, 2, v___x_5650_);
                    v___x_5652_ = v___x_5644_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5655_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5655_, 0, v_env_5635_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5655_, 1, v_nextMacroScope_5636_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5655_, 2, v___x_5650_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5655_, 3, v_auxDeclNGen_5637_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5655_, 4, v_traceState_5638_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5655_, 5, v_cache_5639_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5655_, 6, v_messages_5640_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5655_, 7, v_infoState_5641_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5655_, 8, v_snapshotTasks_5642_);
                    v___x_5652_ = v_reuseFailAlloc_5655_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5653_ = lean_st_ref_set(v___y_5625_, v___x_5652_);
                v___x_5654_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5654_, 0, v_r_5646_);
                return v___x_5654_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg___boxed(
    mut v___y_5660_: *mut leanh::LeanObject,
    mut v___y_5661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5662_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_5660_);
    leanh::lean_dec(v___y_5660_);
    return v_res_5662_;
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(
    mut v___y_5663_: u8,
    mut v___y_5664_: *mut leanh::LeanObject,
    mut v___y_5665_: *mut leanh::LeanObject,
    mut v___y_5666_: *mut leanh::LeanObject,
    mut v___y_5667_: *mut leanh::LeanObject,
    mut v___y_5668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5674_: u8 = 0;
    let mut v___x_5676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5678_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5670_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_5668_);
                v_a_5671_ = leanh::lean_ctor_get(v___x_5670_, 0);
                v_isSharedCheck_5678_ = (!leanh::lean_is_exclusive(v___x_5670_)) as u8;
                if v_isSharedCheck_5678_ == 0 {
                    v___x_5673_ = v___x_5670_;
                    v_isShared_5674_ = v_isSharedCheck_5678_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_5671_);
                    leanh::lean_dec(v___x_5670_);
                    v___x_5673_ = leanh::lean_box(0);
                    v_isShared_5674_ = v_isSharedCheck_5678_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_5674_ == 0 {
                    v___x_5676_ = v___x_5673_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5677_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5677_, 0, v_a_5671_);
                    v___x_5676_ = v_reuseFailAlloc_5677_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5676_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3___boxed(
    mut v___y_5679_: *mut leanh::LeanObject,
    mut v___y_5680_: *mut leanh::LeanObject,
    mut v___y_5681_: *mut leanh::LeanObject,
    mut v___y_5682_: *mut leanh::LeanObject,
    mut v___y_5683_: *mut leanh::LeanObject,
    mut v___y_5684_: *mut leanh::LeanObject,
    mut v___y_5685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_18138__boxed_5686_: u8 = 0;
    let mut v_res_5687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_18138__boxed_5686_ = (leanh::lean_unbox(v___y_5679_) as u8);
    v_res_5687_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(
        v___y_18138__boxed_5686_,
        v___y_5680_,
        v___y_5681_,
        v___y_5682_,
        v___y_5683_,
        v___y_5684_,
    );
    leanh::lean_dec(v___y_5684_);
    leanh::lean_dec_ref(v___y_5683_);
    leanh::lean_dec(v___y_5682_);
    leanh::lean_dec_ref(v___y_5681_);
    leanh::lean_dec(v___y_5680_);
    return v_res_5687_;
}
pub unsafe fn l_Lean_Meta_Closure_collectExprAux___lam__1(
    mut v_e_5688_: *mut leanh::LeanObject,
    mut v_args_5689_: *mut leanh::LeanObject,
    mut v_x_5690_: *mut leanh::LeanObject,
    mut v___y_5691_: u8,
    mut v___y_5692_: *mut leanh::LeanObject,
    mut v___y_5693_: *mut leanh::LeanObject,
    mut v___y_5694_: *mut leanh::LeanObject,
    mut v___y_5695_: *mut leanh::LeanObject,
    mut v___y_5696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: u8 = 0;
    let mut v___x_5700_: u8 = 0;
    let mut v___x_5701_: u8 = 0;
    let mut v___x_5702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5698_ = l_Lean_mkAppN(v_e_5688_, v_args_5689_);
    v___x_5699_ = 0;
    v___x_5700_ = 1;
    v___x_5701_ = 1;
    v___x_5702_ = l_Lean_Meta_mkLambdaFVars(
        v_args_5689_,
        v___x_5698_,
        v___x_5699_,
        v___x_5700_,
        v___x_5699_,
        v___x_5700_,
        v___x_5701_,
        v___y_5693_,
        v___y_5694_,
        v___y_5695_,
        v___y_5696_,
    );
    return v___x_5702_;
}
pub unsafe fn l_Lean_Meta_Closure_collectExprAux___lam__1___boxed(
    mut v_e_5703_: *mut leanh::LeanObject,
    mut v_args_5704_: *mut leanh::LeanObject,
    mut v_x_5705_: *mut leanh::LeanObject,
    mut v___y_5706_: *mut leanh::LeanObject,
    mut v___y_5707_: *mut leanh::LeanObject,
    mut v___y_5708_: *mut leanh::LeanObject,
    mut v___y_5709_: *mut leanh::LeanObject,
    mut v___y_5710_: *mut leanh::LeanObject,
    mut v___y_5711_: *mut leanh::LeanObject,
    mut v___y_5712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_18179__boxed_5713_: u8 = 0;
    let mut v_res_5714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_18179__boxed_5713_ = (leanh::lean_unbox(v___y_5706_) as u8);
    v_res_5714_ = l_Lean_Meta_Closure_collectExprAux___lam__1(
        v_e_5703_,
        v_args_5704_,
        v_x_5705_,
        v___y_18179__boxed_5713_,
        v___y_5707_,
        v___y_5708_,
        v___y_5709_,
        v___y_5710_,
        v___y_5711_,
    );
    leanh::lean_dec(v___y_5711_);
    leanh::lean_dec_ref(v___y_5710_);
    leanh::lean_dec(v___y_5709_);
    leanh::lean_dec_ref(v___y_5708_);
    leanh::lean_dec(v___y_5707_);
    leanh::lean_dec_ref(v_x_5705_);
    leanh::lean_dec_ref(v_args_5704_);
    return v_res_5714_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(
    mut v_x_5715_: *mut leanh::LeanObject,
    mut v_x_5716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_5717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5722_: u8 = 0;
    let mut v___x_5723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5724_: u64 = 0;
    let mut v___x_5725_: u64 = 0;
    let mut v___x_5726_: u64 = 0;
    let mut v_fold_5727_: u64 = 0;
    let mut v___x_5728_: u64 = 0;
    let mut v___x_5729_: u64 = 0;
    let mut v___x_5730_: u64 = 0;
    let mut v___x_5731_: usize = 0;
    let mut v___x_5732_: usize = 0;
    let mut v___x_5733_: usize = 0;
    let mut v___x_5734_: usize = 0;
    let mut v___x_5735_: usize = 0;
    let mut v___x_5736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5742_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5716_) == 0 {
                    return v_x_5715_;
                } else {
                    v_key_5717_ = leanh::lean_ctor_get(v_x_5716_, 0);
                    v_value_5718_ = leanh::lean_ctor_get(v_x_5716_, 1);
                    v_tail_5719_ = leanh::lean_ctor_get(v_x_5716_, 2);
                    v_isSharedCheck_5742_ = (!leanh::lean_is_exclusive(v_x_5716_)) as u8;
                    if v_isSharedCheck_5742_ == 0 {
                        v___x_5721_ = v_x_5716_;
                        v_isShared_5722_ = v_isSharedCheck_5742_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5719_);
                        leanh::lean_inc(v_value_5718_);
                        leanh::lean_inc(v_key_5717_);
                        leanh::lean_dec(v_x_5716_);
                        v___x_5721_ = leanh::lean_box(0);
                        v_isShared_5722_ = v_isSharedCheck_5742_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5723_ = lean_array_get_size(v_x_5715_);
                v___x_5724_ = l_Lean_ExprStructEq_hash(v_key_5717_);
                v___x_5725_ = 32u64;
                v___x_5726_ = lean_uint64_shift_right(v___x_5724_, v___x_5725_);
                v_fold_5727_ = lean_uint64_xor(v___x_5724_, v___x_5726_);
                v___x_5728_ = 16u64;
                v___x_5729_ = lean_uint64_shift_right(v_fold_5727_, v___x_5728_);
                v___x_5730_ = lean_uint64_xor(v_fold_5727_, v___x_5729_);
                v___x_5731_ = lean_uint64_to_usize(v___x_5730_);
                v___x_5732_ = lean_usize_of_nat(v___x_5723_);
                v___x_5733_ = 1usize;
                v___x_5734_ = lean_usize_sub(v___x_5732_, v___x_5733_);
                v___x_5735_ = lean_usize_land(v___x_5731_, v___x_5734_);
                v___x_5736_ = lean_array_uget_borrowed(v_x_5715_, v___x_5735_);
                leanh::lean_inc(v___x_5736_);
                if v_isShared_5722_ == 0 {
                    leanh::lean_ctor_set(v___x_5721_, 2, v___x_5736_);
                    v___x_5738_ = v___x_5721_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5741_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5741_, 0, v_key_5717_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5741_, 1, v_value_5718_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5741_, 2, v___x_5736_);
                    v___x_5738_ = v_reuseFailAlloc_5741_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5739_ = lean_array_uset(v_x_5715_, v___x_5735_, v___x_5738_);
                v_x_5715_ = v___x_5739_;
                v_x_5716_ = v_tail_5719_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(
    mut v_i_5743_: *mut leanh::LeanObject,
    mut v_source_5744_: *mut leanh::LeanObject,
    mut v_target_5745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: u8 = 0;
    let mut v_es_5748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_5750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_5751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5746_ = lean_array_get_size(v_source_5744_);
                v___x_5747_ = lean_nat_dec_lt(v_i_5743_, v___x_5746_);
                if v___x_5747_ == 0 {
                    leanh::lean_dec_ref(v_source_5744_);
                    leanh::lean_dec(v_i_5743_);
                    return v_target_5745_;
                } else {
                    v_es_5748_ = lean_array_fget(v_source_5744_, v_i_5743_);
                    v___x_5749_ = leanh::lean_box(0);
                    v_source_5750_ = lean_array_fset(v_source_5744_, v_i_5743_, v___x_5749_);
                    v_target_5751_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(v_target_5745_, v_es_5748_);
                    v___x_5752_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5753_ = lean_nat_add(v_i_5743_, v___x_5752_);
                    leanh::lean_dec(v_i_5743_);
                    v_i_5743_ = v___x_5753_;
                    v_source_5744_ = v_source_5750_;
                    v_target_5745_ = v_target_5751_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(
    mut v_data_5755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_5758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5756_ = lean_array_get_size(v_data_5755_);
    v___x_5757_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_5758_ = lean_nat_mul(v___x_5756_, v___x_5757_);
    v___x_5759_ = leanh::lean_unsigned_to_nat(0);
    v___x_5760_ = leanh::lean_box(0);
    v___x_5761_ = lean_mk_array(v_nbuckets_5758_, v___x_5760_);
    v___x_5762_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(v___x_5759_, v_data_5755_, v___x_5761_);
    return v___x_5762_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(
    mut v_a_5763_: *mut leanh::LeanObject,
    mut v_b_5764_: *mut leanh::LeanObject,
    mut v_x_5765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_5766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5771_: u8 = 0;
    let mut v___x_5772_: u8 = 0;
    let mut v___x_5773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5780_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5765_) == 0 {
                    leanh::lean_dec(v_b_5764_);
                    leanh::lean_dec_ref(v_a_5763_);
                    return v_x_5765_;
                } else {
                    v_key_5766_ = leanh::lean_ctor_get(v_x_5765_, 0);
                    v_value_5767_ = leanh::lean_ctor_get(v_x_5765_, 1);
                    v_tail_5768_ = leanh::lean_ctor_get(v_x_5765_, 2);
                    v_isSharedCheck_5780_ = (!leanh::lean_is_exclusive(v_x_5765_)) as u8;
                    if v_isSharedCheck_5780_ == 0 {
                        v___x_5770_ = v_x_5765_;
                        v_isShared_5771_ = v_isSharedCheck_5780_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5768_);
                        leanh::lean_inc(v_value_5767_);
                        leanh::lean_inc(v_key_5766_);
                        leanh::lean_dec(v_x_5765_);
                        v___x_5770_ = leanh::lean_box(0);
                        v_isShared_5771_ = v_isSharedCheck_5780_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5772_ = l_Lean_ExprStructEq_beq(v_key_5766_, v_a_5763_);
                if v___x_5772_ == 0 {
                    v___x_5773_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_5763_, v_b_5764_, v_tail_5768_);
                    if v_isShared_5771_ == 0 {
                        leanh::lean_ctor_set(v___x_5770_, 2, v___x_5773_);
                        v___x_5775_ = v___x_5770_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5776_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5776_, 0, v_key_5766_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5776_, 1, v_value_5767_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5776_, 2, v___x_5773_);
                        v___x_5775_ = v_reuseFailAlloc_5776_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_5767_);
                    leanh::lean_dec(v_key_5766_);
                    if v_isShared_5771_ == 0 {
                        leanh::lean_ctor_set(v___x_5770_, 1, v_b_5764_);
                        leanh::lean_ctor_set(v___x_5770_, 0, v_a_5763_);
                        v___x_5778_ = v___x_5770_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5779_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5779_, 0, v_a_5763_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5779_, 1, v_b_5764_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5779_, 2, v_tail_5768_);
                        v___x_5778_ = v_reuseFailAlloc_5779_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5775_;
            }
            3 => {
                return v___x_5778_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(
    mut v_a_5781_: *mut leanh::LeanObject,
    mut v_x_5782_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5783_: u8 = 0;
    let mut v_key_5784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5782_) == 0 {
                    v___x_5783_ = 0;
                    return v___x_5783_;
                } else {
                    v_key_5784_ = leanh::lean_ctor_get(v_x_5782_, 0);
                    v_tail_5785_ = leanh::lean_ctor_get(v_x_5782_, 2);
                    v___x_5786_ = l_Lean_ExprStructEq_beq(v_key_5784_, v_a_5781_);
                    if v___x_5786_ == 0 {
                        v_x_5782_ = v_tail_5785_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5786_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg___boxed(
    mut v_a_5788_: *mut leanh::LeanObject,
    mut v_x_5789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5790_: u8 = 0;
    let mut v_r_5791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5790_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_5788_, v_x_5789_);
    leanh::lean_dec(v_x_5789_);
    leanh::lean_dec_ref(v_a_5788_);
    v_r_5791_ = leanh::lean_box((v_res_5790_) as usize);
    return v_r_5791_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(
    mut v_m_5792_: *mut leanh::LeanObject,
    mut v_a_5793_: *mut leanh::LeanObject,
    mut v_b_5794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_5795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5799_: u8 = 0;
    let mut v___x_5800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: u64 = 0;
    let mut v___x_5802_: u64 = 0;
    let mut v___x_5803_: u64 = 0;
    let mut v_fold_5804_: u64 = 0;
    let mut v___x_5805_: u64 = 0;
    let mut v___x_5806_: u64 = 0;
    let mut v___x_5807_: u64 = 0;
    let mut v___x_5808_: usize = 0;
    let mut v___x_5809_: usize = 0;
    let mut v___x_5810_: usize = 0;
    let mut v___x_5811_: usize = 0;
    let mut v___x_5812_: usize = 0;
    let mut v_bkt_5813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5814_: u8 = 0;
    let mut v___x_5815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_5816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: u8 = 0;
    let mut v_val_5825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5839_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5795_ = leanh::lean_ctor_get(v_m_5792_, 0);
                v_buckets_5796_ = leanh::lean_ctor_get(v_m_5792_, 1);
                v_isSharedCheck_5839_ = (!leanh::lean_is_exclusive(v_m_5792_)) as u8;
                if v_isSharedCheck_5839_ == 0 {
                    v___x_5798_ = v_m_5792_;
                    v_isShared_5799_ = v_isSharedCheck_5839_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_5796_);
                    leanh::lean_inc(v_size_5795_);
                    leanh::lean_dec(v_m_5792_);
                    v___x_5798_ = leanh::lean_box(0);
                    v_isShared_5799_ = v_isSharedCheck_5839_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5800_ = lean_array_get_size(v_buckets_5796_);
                v___x_5801_ = l_Lean_ExprStructEq_hash(v_a_5793_);
                v___x_5802_ = 32u64;
                v___x_5803_ = lean_uint64_shift_right(v___x_5801_, v___x_5802_);
                v_fold_5804_ = lean_uint64_xor(v___x_5801_, v___x_5803_);
                v___x_5805_ = 16u64;
                v___x_5806_ = lean_uint64_shift_right(v_fold_5804_, v___x_5805_);
                v___x_5807_ = lean_uint64_xor(v_fold_5804_, v___x_5806_);
                v___x_5808_ = lean_uint64_to_usize(v___x_5807_);
                v___x_5809_ = lean_usize_of_nat(v___x_5800_);
                v___x_5810_ = 1usize;
                v___x_5811_ = lean_usize_sub(v___x_5809_, v___x_5810_);
                v___x_5812_ = lean_usize_land(v___x_5808_, v___x_5811_);
                v_bkt_5813_ = lean_array_uget_borrowed(v_buckets_5796_, v___x_5812_);
                v___x_5814_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_5793_, v_bkt_5813_);
                if v___x_5814_ == 0 {
                    v___x_5815_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_5816_ = lean_nat_add(v_size_5795_, v___x_5815_);
                    leanh::lean_dec(v_size_5795_);
                    leanh::lean_inc(v_bkt_5813_);
                    v___x_5817_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_5817_, 0, v_a_5793_);
                    leanh::lean_ctor_set(v___x_5817_, 1, v_b_5794_);
                    leanh::lean_ctor_set(v___x_5817_, 2, v_bkt_5813_);
                    v_buckets_x27_5818_ =
                        lean_array_uset(v_buckets_5796_, v___x_5812_, v___x_5817_);
                    v___x_5819_ = leanh::lean_unsigned_to_nat(4);
                    v___x_5820_ = lean_nat_mul(v_size_x27_5816_, v___x_5819_);
                    v___x_5821_ = leanh::lean_unsigned_to_nat(3);
                    v___x_5822_ = lean_nat_div(v___x_5820_, v___x_5821_);
                    leanh::lean_dec(v___x_5820_);
                    v___x_5823_ = lean_array_get_size(v_buckets_x27_5818_);
                    v___x_5824_ = lean_nat_dec_le(v___x_5822_, v___x_5823_);
                    leanh::lean_dec(v___x_5822_);
                    if v___x_5824_ == 0 {
                        v_val_5825_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(v_buckets_x27_5818_);
                        if v_isShared_5799_ == 0 {
                            leanh::lean_ctor_set(v___x_5798_, 1, v_val_5825_);
                            leanh::lean_ctor_set(v___x_5798_, 0, v_size_x27_5816_);
                            v___x_5827_ = v___x_5798_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_5828_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_5828_,
                                0,
                                v_size_x27_5816_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_5828_, 1, v_val_5825_);
                            v___x_5827_ = v_reuseFailAlloc_5828_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_5799_ == 0 {
                            leanh::lean_ctor_set(v___x_5798_, 1, v_buckets_x27_5818_);
                            leanh::lean_ctor_set(v___x_5798_, 0, v_size_x27_5816_);
                            v___x_5830_ = v___x_5798_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5831_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_5831_,
                                0,
                                v_size_x27_5816_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_5831_,
                                1,
                                v_buckets_x27_5818_,
                            );
                            v___x_5830_ = v_reuseFailAlloc_5831_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_5813_);
                    v___x_5832_ = leanh::lean_box(0);
                    v_buckets_x27_5833_ =
                        lean_array_uset(v_buckets_5796_, v___x_5812_, v___x_5832_);
                    v___x_5834_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_5793_, v_b_5794_, v_bkt_5813_);
                    v___x_5835_ = lean_array_uset(v_buckets_x27_5833_, v___x_5812_, v___x_5834_);
                    if v_isShared_5799_ == 0 {
                        leanh::lean_ctor_set(v___x_5798_, 1, v___x_5835_);
                        v___x_5837_ = v___x_5798_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5838_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5838_, 0, v_size_5795_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5838_, 1, v___x_5835_);
                        v___x_5837_ = v_reuseFailAlloc_5838_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5827_;
            }
            3 => {
                return v___x_5830_;
            }
            4 => {
                return v___x_5837_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Closure_collectExprAux(
    mut v_e_5840_: *mut leanh::LeanObject,
    mut v_a_5841_: u8,
    mut v_a_5842_: *mut leanh::LeanObject,
    mut v_a_5843_: *mut leanh::LeanObject,
    mut v_a_5844_: *mut leanh::LeanObject,
    mut v_a_5845_: *mut leanh::LeanObject,
    mut v_a_5846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_typeName_5848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_5849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_5850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5855_: u8 = 0;
    let mut v___x_5856_: usize = 0;
    let mut v___x_5857_: usize = 0;
    let mut v___x_5858_: u8 = 0;
    let mut v___x_5859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5866_: u8 = 0;
    let mut v_binderName_5867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_5868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_5870_: u8 = 0;
    let mut v___x_5871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5877_: u8 = 0;
    let mut v___y_5879_: u8 = 0;
    let mut v___x_5880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5884_: u8 = 0;
    let mut v___x_5885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: usize = 0;
    let mut v___x_5893_: usize = 0;
    let mut v___x_5894_: u8 = 0;
    let mut v___x_5895_: usize = 0;
    let mut v___x_5896_: usize = 0;
    let mut v___x_5897_: u8 = 0;
    let mut v_isSharedCheck_5898_: u8 = 0;
    let mut v_binderName_5899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_5900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_5902_: u8 = 0;
    let mut v___x_5903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5909_: u8 = 0;
    let mut v___y_5911_: u8 = 0;
    let mut v___x_5912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5916_: u8 = 0;
    let mut v___x_5917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5924_: usize = 0;
    let mut v___x_5925_: usize = 0;
    let mut v___x_5926_: u8 = 0;
    let mut v___x_5927_: usize = 0;
    let mut v___x_5928_: usize = 0;
    let mut v___x_5929_: u8 = 0;
    let mut v_isSharedCheck_5930_: u8 = 0;
    let mut v_declName_5931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_5935_: u8 = 0;
    let mut v___x_5936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5944_: u8 = 0;
    let mut v___y_5946_: u8 = 0;
    let mut v___x_5947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: usize = 0;
    let mut v___x_5952_: usize = 0;
    let mut v___x_5953_: u8 = 0;
    let mut v___x_5954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: usize = 0;
    let mut v___x_5962_: usize = 0;
    let mut v___x_5963_: u8 = 0;
    let mut v___x_5964_: usize = 0;
    let mut v___x_5965_: usize = 0;
    let mut v___x_5966_: u8 = 0;
    let mut v_isSharedCheck_5967_: u8 = 0;
    let mut v_fn_5968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5976_: u8 = 0;
    let mut v___y_5978_: u8 = 0;
    let mut v___x_5979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: usize = 0;
    let mut v___x_5987_: usize = 0;
    let mut v___x_5988_: u8 = 0;
    let mut v___x_5989_: usize = 0;
    let mut v___x_5990_: usize = 0;
    let mut v___x_5991_: u8 = 0;
    let mut v_isSharedCheck_5992_: u8 = 0;
    let mut v_data_5993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5999_: u8 = 0;
    let mut v___x_6000_: usize = 0;
    let mut v___x_6001_: usize = 0;
    let mut v___x_6002_: u8 = 0;
    let mut v___x_6003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6010_: u8 = 0;
    let mut v_u_6011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6016_: u8 = 0;
    let mut v___x_6017_: usize = 0;
    let mut v___x_6018_: usize = 0;
    let mut v___x_6019_: u8 = 0;
    let mut v___x_6020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6027_: u8 = 0;
    let mut v_a_6028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6031_: u8 = 0;
    let mut v___x_6033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6035_: u8 = 0;
    let mut v_declName_6036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_6037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6043_: u8 = 0;
    let mut v___x_6044_: u8 = 0;
    let mut v___x_6045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6052_: u8 = 0;
    let mut v_a_6053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6056_: u8 = 0;
    let mut v___x_6058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6060_: u8 = 0;
    let mut v_mvarId_6061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6075_: u8 = 0;
    let mut v_e_x27_6077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_6080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_6081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_6082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextLevelIdx_6083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelArgs_6084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDecls_6085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDeclsForMVars_6086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLetDecls_6087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextExprIdx_6088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprMVarArgs_6089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprFVarArgs_6090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toProcess_6091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6094_: u8 = 0;
    let mut v___x_6095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6096_: u8 = 0;
    let mut v___x_6097_: u8 = 0;
    let mut v___x_6098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6109_: u8 = 0;
    let mut v___x_6110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6115_: u8 = 0;
    let mut v_fvars_6116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: u8 = 0;
    let mut v___x_6122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6125_: u8 = 0;
    let mut v_a_6126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6129_: u8 = 0;
    let mut v___x_6131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6133_: u8 = 0;
    let mut v_isSharedCheck_6134_: u8 = 0;
    let mut v_a_6135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6138_: u8 = 0;
    let mut v___x_6140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6142_: u8 = 0;
    let mut v_a_6143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6146_: u8 = 0;
    let mut v___x_6148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6150_: u8 = 0;
    let mut v_a_6151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6154_: u8 = 0;
    let mut v___x_6156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6158_: u8 = 0;
    let mut v_fvarId_6159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: u8 = 0;
    let mut v___x_6161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6164_: u8 = 0;
    let mut v___y_6165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6176_: u8 = 0;
    let mut v___x_6177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6181_: u8 = 0;
    let mut v_unused_6182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6186_: u8 = 0;
    let mut v___x_6188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6190_: u8 = 0;
    let mut v_a_6191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6194_: u8 = 0;
    let mut v___x_6196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6198_: u8 = 0;
    let mut v_val_6199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6206_: u8 = 0;
    let mut v___x_6208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6210_: u8 = 0;
    let mut v___x_6211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match leanh::lean_obj_tag(v_e_5840_) {
                    11 => {
                        v_typeName_5848_ = leanh::lean_ctor_get(v_e_5840_, 0);
                        v_idx_5849_ = leanh::lean_ctor_get(v_e_5840_, 1);
                        v_struct_5850_ = leanh::lean_ctor_get(v_e_5840_, 2);
                        leanh::lean_inc_ref(v_struct_5850_);
                        v___x_5851_ = l_Lean_Meta_Closure_collectExprAux___lam__0(
                            v_struct_5850_,
                            v_a_5841_,
                            v_a_5842_,
                            v_a_5843_,
                            v_a_5844_,
                            v_a_5845_,
                            v_a_5846_,
                        );
                        if leanh::lean_obj_tag(v___x_5851_) == 0 {
                            v_a_5852_ = leanh::lean_ctor_get(v___x_5851_, 0);
                            v_isSharedCheck_5866_ =
                                (!leanh::lean_is_exclusive(v___x_5851_)) as u8;
                            if v_isSharedCheck_5866_ == 0 {
                                v___x_5854_ = v___x_5851_;
                                v_isShared_5855_ = v_isSharedCheck_5866_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5852_);
                                leanh::lean_dec(v___x_5851_);
                                v___x_5854_ = leanh::lean_box(0);
                                v_isShared_5855_ = v_isSharedCheck_5866_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_e_5840_, 3);
                            return v___x_5851_;
                        }
                    }
                    7 => {
                        v_binderName_5867_ = leanh::lean_ctor_get(v_e_5840_, 0);
                        v_binderType_5868_ = leanh::lean_ctor_get(v_e_5840_, 1);
                        v_body_5869_ = leanh::lean_ctor_get(v_e_5840_, 2);
                        v_binderInfo_5870_ = leanh::lean_ctor_get_uint8(
                            v_e_5840_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                        );
                        leanh::lean_inc_ref(v_binderType_5868_);
                        v___x_5871_ = l_Lean_Meta_Closure_collectExprAux___lam__0(
                            v_binderType_5868_,
                            v_a_5841_,
                            v_a_5842_,
                            v_a_5843_,
                            v_a_5844_,
                            v_a_5845_,
                            v_a_5846_,
                        );
                        if leanh::lean_obj_tag(v___x_5871_) == 0 {
                            v_a_5872_ = leanh::lean_ctor_get(v___x_5871_, 0);
                            leanh::lean_inc(v_a_5872_);
                            leanh::lean_dec_ref_known(v___x_5871_, 1);
                            leanh::lean_inc_ref(v_body_5869_);
                            v___x_5873_ = l_Lean_Meta_Closure_collectExprAux___lam__0(
                                v_body_5869_,
                                v_a_5841_,
                                v_a_5842_,
                                v_a_5843_,
                                v_a_5844_,
                                v_a_5845_,
                                v_a_5846_,
                            );
                            if leanh::lean_obj_tag(v___x_5873_) == 0 {
                                v_a_5874_ = leanh::lean_ctor_get(v___x_5873_, 0);
                                v_isSharedCheck_5898_ =
                                    (!leanh::lean_is_exclusive(v___x_5873_)) as u8;
                                if v_isSharedCheck_5898_ == 0 {
                                    v___x_5876_ = v___x_5873_;
                                    v_isShared_5877_ = v_isSharedCheck_5898_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5874_);
                                    leanh::lean_dec(v___x_5873_);
                                    v___x_5876_ = leanh::lean_box(0);
                                    v_isShared_5877_ = v_isSharedCheck_5898_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_5872_);
                                leanh::lean_dec_ref_known(v_e_5840_, 3);
                                return v___x_5873_;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_e_5840_, 3);
                            return v___x_5871_;
                        }
                    }
                    6 => {
                        v_binderName_5899_ = leanh::lean_ctor_get(v_e_5840_, 0);
                        v_binderType_5900_ = leanh::lean_ctor_get(v_e_5840_, 1);
                        v_body_5901_ = leanh::lean_ctor_get(v_e_5840_, 2);
                        v_binderInfo_5902_ = leanh::lean_ctor_get_uint8(
                            v_e_5840_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                        );
                        leanh::lean_inc_ref(v_binderType_5900_);
                        v___x_5903_ = l_Lean_Meta_Closure_collectExprAux___lam__0(
                            v_binderType_5900_,
                            v_a_5841_,
                            v_a_5842_,
                            v_a_5843_,
                            v_a_5844_,
                            v_a_5845_,
                            v_a_5846_,
                        );
                        if leanh::lean_obj_tag(v___x_5903_) == 0 {
                            v_a_5904_ = leanh::lean_ctor_get(v___x_5903_, 0);
                            leanh::lean_inc(v_a_5904_);
                            leanh::lean_dec_ref_known(v___x_5903_, 1);
                            leanh::lean_inc_ref(v_body_5901_);
                            v___x_5905_ = l_Lean_Meta_Closure_collectExprAux___lam__0(
                                v_body_5901_,
                                v_a_5841_,
                                v_a_5842_,
                                v_a_5843_,
                                v_a_5844_,
                                v_a_5845_,
                                v_a_5846_,
                            );
                            if leanh::lean_obj_tag(v___x_5905_) == 0 {
                                v_a_5906_ = leanh::lean_ctor_get(v___x_5905_, 0);
                                v_isSharedCheck_5930_ =
                                    (!leanh::lean_is_exclusive(v___x_5905_)) as u8;
                                if v_isSharedCheck_5930_ == 0 {
                                    v___x_5908_ = v___x_5905_;
                                    v_isShared_5909_ = v_isSharedCheck_5930_;
                                    state = 9;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5906_);
                                    leanh::lean_dec(v___x_5905_);
                                    v___x_5908_ = leanh::lean_box(0);
                                    v_isShared_5909_ = v_isSharedCheck_5930_;
                                    state = 9;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_5904_);
                                leanh::lean_dec_ref_known(v_e_5840_, 3);
                                return v___x_5905_;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_e_5840_, 3);
                            return v___x_5903_;
                        }
                    }
                    8 => {
                        v_declName_5931_ = leanh::lean_ctor_get(v_e_5840_, 0);
                        v_type_5932_ = leanh::lean_ctor_get(v_e_5840_, 1);
                        v_value_5933_ = leanh::lean_ctor_get(v_e_5840_, 2);
                        v_body_5934_ = leanh::lean_ctor_get(v_e_5840_, 3);
                        v_nondep_5935_ = leanh::lean_ctor_get_uint8(
                            v_e_5840_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8) as u32,
                        );
                        leanh::lean_inc_ref(v_type_5932_);
                        v___x_5936_ = l_Lean_Meta_Closure_collectExprAux___lam__0(
                            v_type_5932_,
                            v_a_5841_,
                            v_a_5842_,
                            v_a_5843_,
                            v_a_5844_,
                            v_a_5845_,
                            v_a_5846_,
                        );
                        if leanh::lean_obj_tag(v___x_5936_) == 0 {
                            v_a_5937_ = leanh::lean_ctor_get(v___x_5936_, 0);
                            leanh::lean_inc(v_a_5937_);
                            leanh::lean_dec_ref_known(v___x_5936_, 1);
                            leanh::lean_inc_ref(v_value_5933_);
                            v___x_5938_ = l_Lean_Meta_Closure_collectExprAux___lam__0(
                                v_value_5933_,
                                v_a_5841_,
                                v_a_5842_,
                                v_a_5843_,
                                v_a_5844_,
                                v_a_5845_,
                                v_a_5846_,
                            );
                            if leanh::lean_obj_tag(v___x_5938_) == 0 {
                                v_a_5939_ = leanh::lean_ctor_get(v___x_5938_, 0);
                                leanh::lean_inc(v_a_5939_);
                                leanh::lean_dec_ref_known(v___x_5938_, 1);
                                leanh::lean_inc_ref(v_body_5934_);
                                v___x_5940_ = l_Lean_Meta_Closure_collectExprAux___lam__0(
                                    v_body_5934_,
                                    v_a_5841_,
                                    v_a_5842_,
                                    v_a_5843_,
                                    v_a_5844_,
                                    v_a_5845_,
                                    v_a_5846_,
                                );
                                if leanh::lean_obj_tag(v___x_5940_) == 0 {
                                    v_a_5941_ = leanh::lean_ctor_get(v___x_5940_, 0);
                                    v_isSharedCheck_5967_ =
                                        (!leanh::lean_is_exclusive(v___x_5940_)) as u8;
                                    if v_isSharedCheck_5967_ == 0 {
                                        v___x_5943_ = v___x_5940_;
                                        v_isShared_5944_ = v_isSharedCheck_5967_;
                                        state = 14;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_5941_);
                                        leanh::lean_dec(v___x_5940_);
                                        v___x_5943_ = leanh::lean_box(0);
                                        v_isShared_5944_ = v_isSharedCheck_5967_;
                                        state = 14;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_5939_);
                                    leanh::lean_dec(v_a_5937_);
                                    leanh::lean_dec_ref_known(v_e_5840_, 4);
                                    return v___x_5940_;
                                }
                            } else {
                                leanh::lean_dec(v_a_5937_);
                                leanh::lean_dec_ref_known(v_e_5840_, 4);
                                return v___x_5938_;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_e_5840_, 4);
                            return v___x_5936_;
                        }
                    }
                    5 => {
                        v_fn_5968_ = leanh::lean_ctor_get(v_e_5840_, 0);
                        v_arg_5969_ = leanh::lean_ctor_get(v_e_5840_, 1);
                        leanh::lean_inc_ref(v_fn_5968_);
                        v___x_5970_ = l_Lean_Meta_Closure_collectExprAux___lam__0(
                            v_fn_5968_, v_a_5841_, v_a_5842_, v_a_5843_, v_a_5844_, v_a_5845_,
                            v_a_5846_,
                        );
                        if leanh::lean_obj_tag(v___x_5970_) == 0 {
                            v_a_5971_ = leanh::lean_ctor_get(v___x_5970_, 0);
                            leanh::lean_inc(v_a_5971_);
                            leanh::lean_dec_ref_known(v___x_5970_, 1);
                            leanh::lean_inc_ref(v_arg_5969_);
                            v___x_5972_ = l_Lean_Meta_Closure_collectExprAux___lam__0(
                                v_arg_5969_,
                                v_a_5841_,
                                v_a_5842_,
                                v_a_5843_,
                                v_a_5844_,
                                v_a_5845_,
                                v_a_5846_,
                            );
                            if leanh::lean_obj_tag(v___x_5972_) == 0 {
                                v_a_5973_ = leanh::lean_ctor_get(v___x_5972_, 0);
                                v_isSharedCheck_5992_ =
                                    (!leanh::lean_is_exclusive(v___x_5972_)) as u8;
                                if v_isSharedCheck_5992_ == 0 {
                                    v___x_5975_ = v___x_5972_;
                                    v_isShared_5976_ = v_isSharedCheck_5992_;
                                    state = 19;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5973_);
                                    leanh::lean_dec(v___x_5972_);
                                    v___x_5975_ = leanh::lean_box(0);
                                    v_isShared_5976_ = v_isSharedCheck_5992_;
                                    state = 19;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_5971_);
                                leanh::lean_dec_ref_known(v_e_5840_, 2);
                                return v___x_5972_;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_e_5840_, 2);
                            return v___x_5970_;
                        }
                    }
                    10 => {
                        v_data_5993_ = leanh::lean_ctor_get(v_e_5840_, 0);
                        v_expr_5994_ = leanh::lean_ctor_get(v_e_5840_, 1);
                        leanh::lean_inc_ref(v_expr_5994_);
                        v___x_5995_ = l_Lean_Meta_Closure_collectExprAux___lam__0(
                            v_expr_5994_,
                            v_a_5841_,
                            v_a_5842_,
                            v_a_5843_,
                            v_a_5844_,
                            v_a_5845_,
                            v_a_5846_,
                        );
                        if leanh::lean_obj_tag(v___x_5995_) == 0 {
                            v_a_5996_ = leanh::lean_ctor_get(v___x_5995_, 0);
                            v_isSharedCheck_6010_ =
                                (!leanh::lean_is_exclusive(v___x_5995_)) as u8;
                            if v_isSharedCheck_6010_ == 0 {
                                v___x_5998_ = v___x_5995_;
                                v_isShared_5999_ = v_isSharedCheck_6010_;
                                state = 23;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5996_);
                                leanh::lean_dec(v___x_5995_);
                                v___x_5998_ = leanh::lean_box(0);
                                v_isShared_5999_ = v_isSharedCheck_6010_;
                                state = 23;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_e_5840_, 2);
                            return v___x_5995_;
                        }
                    }
                    3 => {
                        v_u_6011_ = leanh::lean_ctor_get(v_e_5840_, 0);
                        leanh::lean_inc(v_u_6011_);
                        v___x_6012_ =
                            l_Lean_Meta_Closure_collectLevel___redArg(v_u_6011_, v_a_5842_);
                        if leanh::lean_obj_tag(v___x_6012_) == 0 {
                            v_a_6013_ = leanh::lean_ctor_get(v___x_6012_, 0);
                            v_isSharedCheck_6027_ =
                                (!leanh::lean_is_exclusive(v___x_6012_)) as u8;
                            if v_isSharedCheck_6027_ == 0 {
                                v___x_6015_ = v___x_6012_;
                                v_isShared_6016_ = v_isSharedCheck_6027_;
                                state = 26;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6013_);
                                leanh::lean_dec(v___x_6012_);
                                v___x_6015_ = leanh::lean_box(0);
                                v_isShared_6016_ = v_isSharedCheck_6027_;
                                state = 26;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_e_5840_, 1);
                            v_a_6028_ = leanh::lean_ctor_get(v___x_6012_, 0);
                            v_isSharedCheck_6035_ =
                                (!leanh::lean_is_exclusive(v___x_6012_)) as u8;
                            if v_isSharedCheck_6035_ == 0 {
                                v___x_6030_ = v___x_6012_;
                                v_isShared_6031_ = v_isSharedCheck_6035_;
                                state = 29;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6028_);
                                leanh::lean_dec(v___x_6012_);
                                v___x_6030_ = leanh::lean_box(0);
                                v_isShared_6031_ = v_isSharedCheck_6035_;
                                state = 29;
                                continue;
                            }
                        }
                    }
                    4 => {
                        v_declName_6036_ = leanh::lean_ctor_get(v_e_5840_, 0);
                        v_us_6037_ = leanh::lean_ctor_get(v_e_5840_, 1);
                        v___x_6038_ = leanh::lean_box(0);
                        leanh::lean_inc(v_us_6037_);
                        v___x_6039_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_us_6037_, v___x_6038_, v_a_5842_);
                        if leanh::lean_obj_tag(v___x_6039_) == 0 {
                            v_a_6040_ = leanh::lean_ctor_get(v___x_6039_, 0);
                            v_isSharedCheck_6052_ =
                                (!leanh::lean_is_exclusive(v___x_6039_)) as u8;
                            if v_isSharedCheck_6052_ == 0 {
                                v___x_6042_ = v___x_6039_;
                                v_isShared_6043_ = v_isSharedCheck_6052_;
                                state = 31;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6040_);
                                leanh::lean_dec(v___x_6039_);
                                v___x_6042_ = leanh::lean_box(0);
                                v_isShared_6043_ = v_isSharedCheck_6052_;
                                state = 31;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_e_5840_, 2);
                            v_a_6053_ = leanh::lean_ctor_get(v___x_6039_, 0);
                            v_isSharedCheck_6060_ =
                                (!leanh::lean_is_exclusive(v___x_6039_)) as u8;
                            if v_isSharedCheck_6060_ == 0 {
                                v___x_6055_ = v___x_6039_;
                                v_isShared_6056_ = v_isSharedCheck_6060_;
                                state = 34;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6053_);
                                leanh::lean_dec(v___x_6039_);
                                v___x_6055_ = leanh::lean_box(0);
                                v_isShared_6056_ = v_isSharedCheck_6060_;
                                state = 34;
                                continue;
                            }
                        }
                    }
                    2 => {
                        v_mvarId_6061_ = leanh::lean_ctor_get(v_e_5840_, 0);
                        leanh::lean_inc(v_mvarId_6061_);
                        v___x_6062_ = l_Lean_MVarId_getDecl(
                            v_mvarId_6061_,
                            v_a_5843_,
                            v_a_5844_,
                            v_a_5845_,
                            v_a_5846_,
                        );
                        if leanh::lean_obj_tag(v___x_6062_) == 0 {
                            v_a_6063_ = leanh::lean_ctor_get(v___x_6062_, 0);
                            leanh::lean_inc(v_a_6063_);
                            leanh::lean_dec_ref_known(v___x_6062_, 1);
                            v_type_6064_ = leanh::lean_ctor_get(v_a_6063_, 2);
                            leanh::lean_inc_ref_n(v_type_6064_, 2);
                            leanh::lean_dec(v_a_6063_);
                            v___x_6065_ = l_Lean_Meta_Closure_preprocess(
                                v_type_6064_,
                                v_a_5841_,
                                v_a_5842_,
                                v_a_5843_,
                                v_a_5844_,
                                v_a_5845_,
                                v_a_5846_,
                            );
                            if leanh::lean_obj_tag(v___x_6065_) == 0 {
                                v_a_6066_ = leanh::lean_ctor_get(v___x_6065_, 0);
                                leanh::lean_inc(v_a_6066_);
                                leanh::lean_dec_ref_known(v___x_6065_, 1);
                                v___x_6067_ = l_Lean_Meta_Closure_collectExprAux___lam__0(
                                    v_a_6066_, v_a_5841_, v_a_5842_, v_a_5843_, v_a_5844_,
                                    v_a_5845_, v_a_5846_,
                                );
                                if leanh::lean_obj_tag(v___x_6067_) == 0 {
                                    v_a_6068_ = leanh::lean_ctor_get(v___x_6067_, 0);
                                    leanh::lean_inc(v_a_6068_);
                                    leanh::lean_dec_ref_known(v___x_6067_, 1);
                                    v___x_6069_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v_a_5841_, v_a_5842_, v_a_5843_, v_a_5844_, v_a_5845_, v_a_5846_);
                                    if leanh::lean_obj_tag(v___x_6069_) == 0 {
                                        v_a_6070_ = leanh::lean_ctor_get(v___x_6069_, 0);
                                        leanh::lean_inc(v_a_6070_);
                                        leanh::lean_dec_ref_known(v___x_6069_, 1);
                                        v___x_6071_ =
                                            l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_5842_);
                                        if leanh::lean_obj_tag(v___x_6071_) == 0 {
                                            v_a_6072_ = leanh::lean_ctor_get(v___x_6071_, 0);
                                            v_isSharedCheck_6134_ =
                                                (!leanh::lean_is_exclusive(v___x_6071_))
                                                    as u8;
                                            if v_isSharedCheck_6134_ == 0 {
                                                v___x_6074_ = v___x_6071_;
                                                v_isShared_6075_ = v_isSharedCheck_6134_;
                                                state = 36;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_6072_);
                                                leanh::lean_dec(v___x_6071_);
                                                v___x_6074_ = leanh::lean_box(0);
                                                v_isShared_6075_ = v_isSharedCheck_6134_;
                                                state = 36;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec(v_a_6070_);
                                            leanh::lean_dec(v_a_6068_);
                                            leanh::lean_dec_ref(v_type_6064_);
                                            leanh::lean_dec_ref_known(v_e_5840_, 1);
                                            v_a_6135_ = leanh::lean_ctor_get(v___x_6071_, 0);
                                            v_isSharedCheck_6142_ =
                                                (!leanh::lean_is_exclusive(v___x_6071_))
                                                    as u8;
                                            if v_isSharedCheck_6142_ == 0 {
                                                v___x_6137_ = v___x_6071_;
                                                v_isShared_6138_ = v_isSharedCheck_6142_;
                                                state = 45;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_6135_);
                                                leanh::lean_dec(v___x_6071_);
                                                v___x_6137_ = leanh::lean_box(0);
                                                v_isShared_6138_ = v_isSharedCheck_6142_;
                                                state = 45;
                                                continue;
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_6068_);
                                        leanh::lean_dec_ref(v_type_6064_);
                                        leanh::lean_dec_ref_known(v_e_5840_, 1);
                                        v_a_6143_ = leanh::lean_ctor_get(v___x_6069_, 0);
                                        v_isSharedCheck_6150_ =
                                            (!leanh::lean_is_exclusive(v___x_6069_)) as u8;
                                        if v_isSharedCheck_6150_ == 0 {
                                            v___x_6145_ = v___x_6069_;
                                            v_isShared_6146_ = v_isSharedCheck_6150_;
                                            state = 47;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_6143_);
                                            leanh::lean_dec(v___x_6069_);
                                            v___x_6145_ = leanh::lean_box(0);
                                            v_isShared_6146_ = v_isSharedCheck_6150_;
                                            state = 47;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_type_6064_);
                                    leanh::lean_dec_ref_known(v_e_5840_, 1);
                                    return v___x_6067_;
                                }
                            } else {
                                leanh::lean_dec_ref(v_type_6064_);
                                leanh::lean_dec_ref_known(v_e_5840_, 1);
                                return v___x_6065_;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_e_5840_, 1);
                            v_a_6151_ = leanh::lean_ctor_get(v___x_6062_, 0);
                            v_isSharedCheck_6158_ =
                                (!leanh::lean_is_exclusive(v___x_6062_)) as u8;
                            if v_isSharedCheck_6158_ == 0 {
                                v___x_6153_ = v___x_6062_;
                                v_isShared_6154_ = v_isSharedCheck_6158_;
                                state = 49;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6151_);
                                leanh::lean_dec(v___x_6062_);
                                v___x_6153_ = leanh::lean_box(0);
                                v_isShared_6154_ = v_isSharedCheck_6158_;
                                state = 49;
                                continue;
                            }
                        }
                    }
                    1 => {
                        v_fvarId_6159_ = leanh::lean_ctor_get(v_e_5840_, 0);
                        leanh::lean_inc_n(v_fvarId_6159_, 2);
                        leanh::lean_dec_ref_known(v_e_5840_, 1);
                        v___x_6160_ = 0;
                        v___x_6161_ = l_Lean_FVarId_getValue_x3f___redArg(
                            v_fvarId_6159_,
                            v___x_6160_,
                            v_a_5843_,
                            v_a_5845_,
                            v_a_5846_,
                        );
                        if leanh::lean_obj_tag(v___x_6161_) == 0 {
                            v_a_6162_ = leanh::lean_ctor_get(v___x_6161_, 0);
                            leanh::lean_inc(v_a_6162_);
                            leanh::lean_dec_ref_known(v___x_6161_, 1);
                            if v_a_5841_ == 1 {
                                if leanh::lean_obj_tag(v_a_6162_) == 1 {
                                    leanh::lean_dec(v_fvarId_6159_);
                                    v_val_6199_ = leanh::lean_ctor_get(v_a_6162_, 0);
                                    leanh::lean_inc(v_val_6199_);
                                    leanh::lean_dec_ref_known(v_a_6162_, 1);
                                    v___x_6200_ = l_Lean_Meta_Closure_preprocess(
                                        v_val_6199_,
                                        v_a_5841_,
                                        v_a_5842_,
                                        v_a_5843_,
                                        v_a_5844_,
                                        v_a_5845_,
                                        v_a_5846_,
                                    );
                                    if leanh::lean_obj_tag(v___x_6200_) == 0 {
                                        v_a_6201_ = leanh::lean_ctor_get(v___x_6200_, 0);
                                        leanh::lean_inc(v_a_6201_);
                                        leanh::lean_dec_ref_known(v___x_6200_, 1);
                                        v___x_6202_ = l_Lean_Meta_Closure_collectExprAux___lam__0(
                                            v_a_6201_, v_a_5841_, v_a_5842_, v_a_5843_, v_a_5844_,
                                            v_a_5845_, v_a_5846_,
                                        );
                                        return v___x_6202_;
                                    } else {
                                        return v___x_6200_;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_6162_);
                                    v___y_6164_ = v_a_5841_;
                                    v___y_6165_ = v_a_5842_;
                                    v___y_6166_ = v_a_5843_;
                                    v___y_6167_ = v_a_5844_;
                                    v___y_6168_ = v_a_5845_;
                                    v___y_6169_ = v_a_5846_;
                                    state = 51;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_6162_);
                                v___y_6164_ = v_a_5841_;
                                v___y_6165_ = v_a_5842_;
                                v___y_6166_ = v_a_5843_;
                                v___y_6167_ = v_a_5844_;
                                v___y_6168_ = v_a_5845_;
                                v___y_6169_ = v_a_5846_;
                                state = 51;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_fvarId_6159_);
                            v_a_6203_ = leanh::lean_ctor_get(v___x_6161_, 0);
                            v_isSharedCheck_6210_ =
                                (!leanh::lean_is_exclusive(v___x_6161_)) as u8;
                            if v_isSharedCheck_6210_ == 0 {
                                v___x_6205_ = v___x_6161_;
                                v_isShared_6206_ = v_isSharedCheck_6210_;
                                state = 58;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6203_);
                                leanh::lean_dec(v___x_6161_);
                                v___x_6205_ = leanh::lean_box(0);
                                v_isShared_6206_ = v_isSharedCheck_6210_;
                                state = 58;
                                continue;
                            }
                        }
                    }
                    _ => {
                        v___x_6211_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_6211_, 0, v_e_5840_);
                        return v___x_6211_;
                    }
                }
            }
            1 => {
                v___x_5856_ = lean_ptr_addr(v_struct_5850_);
                v___x_5857_ = lean_ptr_addr(v_a_5852_);
                v___x_5858_ = lean_usize_dec_eq(v___x_5856_, v___x_5857_);
                if v___x_5858_ == 0 {
                    leanh::lean_inc(v_idx_5849_);
                    leanh::lean_inc(v_typeName_5848_);
                    leanh::lean_dec_ref_known(v_e_5840_, 3);
                    v___x_5859_ =
                        l_Lean_Expr_proj___override(v_typeName_5848_, v_idx_5849_, v_a_5852_);
                    if v_isShared_5855_ == 0 {
                        leanh::lean_ctor_set(v___x_5854_, 0, v___x_5859_);
                        v___x_5861_ = v___x_5854_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5862_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5862_, 0, v___x_5859_);
                        v___x_5861_ = v_reuseFailAlloc_5862_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_5852_);
                    if v_isShared_5855_ == 0 {
                        leanh::lean_ctor_set(v___x_5854_, 0, v_e_5840_);
                        v___x_5864_ = v___x_5854_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5865_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5865_, 0, v_e_5840_);
                        v___x_5864_ = v_reuseFailAlloc_5865_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5861_;
            }
            3 => {
                return v___x_5864_;
            }
            4 => {
                v___x_5892_ = lean_ptr_addr(v_binderType_5868_);
                v___x_5893_ = lean_ptr_addr(v_a_5872_);
                v___x_5894_ = lean_usize_dec_eq(v___x_5892_, v___x_5893_);
                if v___x_5894_ == 0 {
                    v___y_5879_ = v___x_5894_;
                    state = 5;
                    continue;
                } else {
                    v___x_5895_ = lean_ptr_addr(v_body_5869_);
                    v___x_5896_ = lean_ptr_addr(v_a_5874_);
                    v___x_5897_ = lean_usize_dec_eq(v___x_5895_, v___x_5896_);
                    v___y_5879_ = v___x_5897_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v___y_5879_ == 0 {
                    leanh::lean_inc(v_binderName_5867_);
                    leanh::lean_dec_ref_known(v_e_5840_, 3);
                    v___x_5880_ = l_Lean_Expr_forallE___override(
                        v_binderName_5867_,
                        v_a_5872_,
                        v_a_5874_,
                        v_binderInfo_5870_,
                    );
                    if v_isShared_5877_ == 0 {
                        leanh::lean_ctor_set(v___x_5876_, 0, v___x_5880_);
                        v___x_5882_ = v___x_5876_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_5883_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5883_, 0, v___x_5880_);
                        v___x_5882_ = v_reuseFailAlloc_5883_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_5884_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_5870_, v_binderInfo_5870_);
                    if v___x_5884_ == 0 {
                        leanh::lean_inc(v_binderName_5867_);
                        leanh::lean_dec_ref_known(v_e_5840_, 3);
                        v___x_5885_ = l_Lean_Expr_forallE___override(
                            v_binderName_5867_,
                            v_a_5872_,
                            v_a_5874_,
                            v_binderInfo_5870_,
                        );
                        if v_isShared_5877_ == 0 {
                            leanh::lean_ctor_set(v___x_5876_, 0, v___x_5885_);
                            v___x_5887_ = v___x_5876_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_5888_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5888_, 0, v___x_5885_);
                            v___x_5887_ = v_reuseFailAlloc_5888_;
                            state = 7;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_5874_);
                        leanh::lean_dec(v_a_5872_);
                        if v_isShared_5877_ == 0 {
                            leanh::lean_ctor_set(v___x_5876_, 0, v_e_5840_);
                            v___x_5890_ = v___x_5876_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_5891_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5891_, 0, v_e_5840_);
                            v___x_5890_ = v_reuseFailAlloc_5891_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            6 => {
                return v___x_5882_;
            }
            7 => {
                return v___x_5887_;
            }
            8 => {
                return v___x_5890_;
            }
            9 => {
                v___x_5924_ = lean_ptr_addr(v_binderType_5900_);
                v___x_5925_ = lean_ptr_addr(v_a_5904_);
                v___x_5926_ = lean_usize_dec_eq(v___x_5924_, v___x_5925_);
                if v___x_5926_ == 0 {
                    v___y_5911_ = v___x_5926_;
                    state = 10;
                    continue;
                } else {
                    v___x_5927_ = lean_ptr_addr(v_body_5901_);
                    v___x_5928_ = lean_ptr_addr(v_a_5906_);
                    v___x_5929_ = lean_usize_dec_eq(v___x_5927_, v___x_5928_);
                    v___y_5911_ = v___x_5929_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_5911_ == 0 {
                    leanh::lean_inc(v_binderName_5899_);
                    leanh::lean_dec_ref_known(v_e_5840_, 3);
                    v___x_5912_ = l_Lean_Expr_lam___override(
                        v_binderName_5899_,
                        v_a_5904_,
                        v_a_5906_,
                        v_binderInfo_5902_,
                    );
                    if v_isShared_5909_ == 0 {
                        leanh::lean_ctor_set(v___x_5908_, 0, v___x_5912_);
                        v___x_5914_ = v___x_5908_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_5915_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5915_, 0, v___x_5912_);
                        v___x_5914_ = v_reuseFailAlloc_5915_;
                        state = 11;
                        continue;
                    }
                } else {
                    v___x_5916_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_5902_, v_binderInfo_5902_);
                    if v___x_5916_ == 0 {
                        leanh::lean_inc(v_binderName_5899_);
                        leanh::lean_dec_ref_known(v_e_5840_, 3);
                        v___x_5917_ = l_Lean_Expr_lam___override(
                            v_binderName_5899_,
                            v_a_5904_,
                            v_a_5906_,
                            v_binderInfo_5902_,
                        );
                        if v_isShared_5909_ == 0 {
                            leanh::lean_ctor_set(v___x_5908_, 0, v___x_5917_);
                            v___x_5919_ = v___x_5908_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_5920_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5920_, 0, v___x_5917_);
                            v___x_5919_ = v_reuseFailAlloc_5920_;
                            state = 12;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_5906_);
                        leanh::lean_dec(v_a_5904_);
                        if v_isShared_5909_ == 0 {
                            leanh::lean_ctor_set(v___x_5908_, 0, v_e_5840_);
                            v___x_5922_ = v___x_5908_;
                            state = 13;
                            continue;
                        } else {
                            v_reuseFailAlloc_5923_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5923_, 0, v_e_5840_);
                            v___x_5922_ = v_reuseFailAlloc_5923_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            11 => {
                return v___x_5914_;
            }
            12 => {
                return v___x_5919_;
            }
            13 => {
                return v___x_5922_;
            }
            14 => {
                v___x_5961_ = lean_ptr_addr(v_type_5932_);
                v___x_5962_ = lean_ptr_addr(v_a_5937_);
                v___x_5963_ = lean_usize_dec_eq(v___x_5961_, v___x_5962_);
                if v___x_5963_ == 0 {
                    v___y_5946_ = v___x_5963_;
                    state = 15;
                    continue;
                } else {
                    v___x_5964_ = lean_ptr_addr(v_value_5933_);
                    v___x_5965_ = lean_ptr_addr(v_a_5939_);
                    v___x_5966_ = lean_usize_dec_eq(v___x_5964_, v___x_5965_);
                    v___y_5946_ = v___x_5966_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v___y_5946_ == 0 {
                    leanh::lean_inc(v_declName_5931_);
                    leanh::lean_dec_ref_known(v_e_5840_, 4);
                    v___x_5947_ = l_Lean_Expr_letE___override(
                        v_declName_5931_,
                        v_a_5937_,
                        v_a_5939_,
                        v_a_5941_,
                        v_nondep_5935_,
                    );
                    if v_isShared_5944_ == 0 {
                        leanh::lean_ctor_set(v___x_5943_, 0, v___x_5947_);
                        v___x_5949_ = v___x_5943_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_5950_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5950_, 0, v___x_5947_);
                        v___x_5949_ = v_reuseFailAlloc_5950_;
                        state = 16;
                        continue;
                    }
                } else {
                    v___x_5951_ = lean_ptr_addr(v_body_5934_);
                    v___x_5952_ = lean_ptr_addr(v_a_5941_);
                    v___x_5953_ = lean_usize_dec_eq(v___x_5951_, v___x_5952_);
                    if v___x_5953_ == 0 {
                        leanh::lean_inc(v_declName_5931_);
                        leanh::lean_dec_ref_known(v_e_5840_, 4);
                        v___x_5954_ = l_Lean_Expr_letE___override(
                            v_declName_5931_,
                            v_a_5937_,
                            v_a_5939_,
                            v_a_5941_,
                            v_nondep_5935_,
                        );
                        if v_isShared_5944_ == 0 {
                            leanh::lean_ctor_set(v___x_5943_, 0, v___x_5954_);
                            v___x_5956_ = v___x_5943_;
                            state = 17;
                            continue;
                        } else {
                            v_reuseFailAlloc_5957_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5957_, 0, v___x_5954_);
                            v___x_5956_ = v_reuseFailAlloc_5957_;
                            state = 17;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_5941_);
                        leanh::lean_dec(v_a_5939_);
                        leanh::lean_dec(v_a_5937_);
                        if v_isShared_5944_ == 0 {
                            leanh::lean_ctor_set(v___x_5943_, 0, v_e_5840_);
                            v___x_5959_ = v___x_5943_;
                            state = 18;
                            continue;
                        } else {
                            v_reuseFailAlloc_5960_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5960_, 0, v_e_5840_);
                            v___x_5959_ = v_reuseFailAlloc_5960_;
                            state = 18;
                            continue;
                        }
                    }
                }
            }
            16 => {
                return v___x_5949_;
            }
            17 => {
                return v___x_5956_;
            }
            18 => {
                return v___x_5959_;
            }
            19 => {
                v___x_5986_ = lean_ptr_addr(v_fn_5968_);
                v___x_5987_ = lean_ptr_addr(v_a_5971_);
                v___x_5988_ = lean_usize_dec_eq(v___x_5986_, v___x_5987_);
                if v___x_5988_ == 0 {
                    v___y_5978_ = v___x_5988_;
                    state = 20;
                    continue;
                } else {
                    v___x_5989_ = lean_ptr_addr(v_arg_5969_);
                    v___x_5990_ = lean_ptr_addr(v_a_5973_);
                    v___x_5991_ = lean_usize_dec_eq(v___x_5989_, v___x_5990_);
                    v___y_5978_ = v___x_5991_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v___y_5978_ == 0 {
                    leanh::lean_dec_ref_known(v_e_5840_, 2);
                    v___x_5979_ = l_Lean_Expr_app___override(v_a_5971_, v_a_5973_);
                    if v_isShared_5976_ == 0 {
                        leanh::lean_ctor_set(v___x_5975_, 0, v___x_5979_);
                        v___x_5981_ = v___x_5975_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_5982_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5982_, 0, v___x_5979_);
                        v___x_5981_ = v_reuseFailAlloc_5982_;
                        state = 21;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_5973_);
                    leanh::lean_dec(v_a_5971_);
                    if v_isShared_5976_ == 0 {
                        leanh::lean_ctor_set(v___x_5975_, 0, v_e_5840_);
                        v___x_5984_ = v___x_5975_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_5985_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5985_, 0, v_e_5840_);
                        v___x_5984_ = v_reuseFailAlloc_5985_;
                        state = 22;
                        continue;
                    }
                }
            }
            21 => {
                return v___x_5981_;
            }
            22 => {
                return v___x_5984_;
            }
            23 => {
                v___x_6000_ = lean_ptr_addr(v_expr_5994_);
                v___x_6001_ = lean_ptr_addr(v_a_5996_);
                v___x_6002_ = lean_usize_dec_eq(v___x_6000_, v___x_6001_);
                if v___x_6002_ == 0 {
                    leanh::lean_inc(v_data_5993_);
                    leanh::lean_dec_ref_known(v_e_5840_, 2);
                    v___x_6003_ = l_Lean_Expr_mdata___override(v_data_5993_, v_a_5996_);
                    if v_isShared_5999_ == 0 {
                        leanh::lean_ctor_set(v___x_5998_, 0, v___x_6003_);
                        v___x_6005_ = v___x_5998_;
                        state = 24;
                        continue;
                    } else {
                        v_reuseFailAlloc_6006_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6006_, 0, v___x_6003_);
                        v___x_6005_ = v_reuseFailAlloc_6006_;
                        state = 24;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_5996_);
                    if v_isShared_5999_ == 0 {
                        leanh::lean_ctor_set(v___x_5998_, 0, v_e_5840_);
                        v___x_6008_ = v___x_5998_;
                        state = 25;
                        continue;
                    } else {
                        v_reuseFailAlloc_6009_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6009_, 0, v_e_5840_);
                        v___x_6008_ = v_reuseFailAlloc_6009_;
                        state = 25;
                        continue;
                    }
                }
            }
            24 => {
                return v___x_6005_;
            }
            25 => {
                return v___x_6008_;
            }
            26 => {
                v___x_6017_ = lean_ptr_addr(v_u_6011_);
                v___x_6018_ = lean_ptr_addr(v_a_6013_);
                v___x_6019_ = lean_usize_dec_eq(v___x_6017_, v___x_6018_);
                if v___x_6019_ == 0 {
                    leanh::lean_dec_ref_known(v_e_5840_, 1);
                    v___x_6020_ = l_Lean_Expr_sort___override(v_a_6013_);
                    if v_isShared_6016_ == 0 {
                        leanh::lean_ctor_set(v___x_6015_, 0, v___x_6020_);
                        v___x_6022_ = v___x_6015_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_6023_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6023_, 0, v___x_6020_);
                        v___x_6022_ = v_reuseFailAlloc_6023_;
                        state = 27;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_6013_);
                    if v_isShared_6016_ == 0 {
                        leanh::lean_ctor_set(v___x_6015_, 0, v_e_5840_);
                        v___x_6025_ = v___x_6015_;
                        state = 28;
                        continue;
                    } else {
                        v_reuseFailAlloc_6026_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6026_, 0, v_e_5840_);
                        v___x_6025_ = v_reuseFailAlloc_6026_;
                        state = 28;
                        continue;
                    }
                }
            }
            27 => {
                return v___x_6022_;
            }
            28 => {
                return v___x_6025_;
            }
            29 => {
                if v_isShared_6031_ == 0 {
                    v___x_6033_ = v___x_6030_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_6034_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6034_, 0, v_a_6028_);
                    v___x_6033_ = v_reuseFailAlloc_6034_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_6033_;
            }
            31 => {
                v___x_6044_ = l_ptrEqList___redArg(v_us_6037_, v_a_6040_);
                if v___x_6044_ == 0 {
                    leanh::lean_inc(v_declName_6036_);
                    leanh::lean_dec_ref_known(v_e_5840_, 2);
                    v___x_6045_ = l_Lean_Expr_const___override(v_declName_6036_, v_a_6040_);
                    if v_isShared_6043_ == 0 {
                        leanh::lean_ctor_set(v___x_6042_, 0, v___x_6045_);
                        v___x_6047_ = v___x_6042_;
                        state = 32;
                        continue;
                    } else {
                        v_reuseFailAlloc_6048_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6048_, 0, v___x_6045_);
                        v___x_6047_ = v_reuseFailAlloc_6048_;
                        state = 32;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_6040_);
                    if v_isShared_6043_ == 0 {
                        leanh::lean_ctor_set(v___x_6042_, 0, v_e_5840_);
                        v___x_6050_ = v___x_6042_;
                        state = 33;
                        continue;
                    } else {
                        v_reuseFailAlloc_6051_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6051_, 0, v_e_5840_);
                        v___x_6050_ = v_reuseFailAlloc_6051_;
                        state = 33;
                        continue;
                    }
                }
            }
            32 => {
                return v___x_6047_;
            }
            33 => {
                return v___x_6050_;
            }
            34 => {
                if v_isShared_6056_ == 0 {
                    v___x_6058_ = v___x_6055_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_6059_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6059_, 0, v_a_6053_);
                    v___x_6058_ = v_reuseFailAlloc_6059_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_6058_;
            }
            36 => {
                v___x_6110_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_6061_, v_a_5844_);
                if leanh::lean_obj_tag(v___x_6110_) == 0 {
                    v_a_6111_ = leanh::lean_ctor_get(v___x_6110_, 0);
                    leanh::lean_inc(v_a_6111_);
                    leanh::lean_dec_ref_known(v___x_6110_, 1);
                    if leanh::lean_obj_tag(v_a_6111_) == 1 {
                        v_val_6112_ = leanh::lean_ctor_get(v_a_6111_, 0);
                        v_isSharedCheck_6125_ = (!leanh::lean_is_exclusive(v_a_6111_)) as u8;
                        if v_isSharedCheck_6125_ == 0 {
                            v___x_6114_ = v_a_6111_;
                            v_isShared_6115_ = v_isSharedCheck_6125_;
                            state = 41;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_6112_);
                            leanh::lean_dec(v_a_6111_);
                            v___x_6114_ = leanh::lean_box(0);
                            v_isShared_6115_ = v_isSharedCheck_6125_;
                            state = 41;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_6111_);
                        leanh::lean_dec_ref(v_type_6064_);
                        v_e_x27_6077_ = v_e_5840_;
                        v___y_6078_ = v_a_5842_;
                        state = 37;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6074_);
                    leanh::lean_dec(v_a_6072_);
                    leanh::lean_dec(v_a_6070_);
                    leanh::lean_dec(v_a_6068_);
                    leanh::lean_dec_ref(v_type_6064_);
                    leanh::lean_dec_ref_known(v_e_5840_, 1);
                    v_a_6126_ = leanh::lean_ctor_get(v___x_6110_, 0);
                    v_isSharedCheck_6133_ = (!leanh::lean_is_exclusive(v___x_6110_)) as u8;
                    if v_isSharedCheck_6133_ == 0 {
                        v___x_6128_ = v___x_6110_;
                        v_isShared_6129_ = v_isSharedCheck_6133_;
                        state = 43;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6126_);
                        leanh::lean_dec(v___x_6110_);
                        v___x_6128_ = leanh::lean_box(0);
                        v_isShared_6129_ = v_isSharedCheck_6133_;
                        state = 43;
                        continue;
                    }
                }
            }
            37 => {
                v___x_6079_ = lean_st_ref_take(v___y_6078_);
                v_visitedLevel_6080_ = leanh::lean_ctor_get(v___x_6079_, 0);
                v_visitedExpr_6081_ = leanh::lean_ctor_get(v___x_6079_, 1);
                v_levelParams_6082_ = leanh::lean_ctor_get(v___x_6079_, 2);
                v_nextLevelIdx_6083_ = leanh::lean_ctor_get(v___x_6079_, 3);
                v_levelArgs_6084_ = leanh::lean_ctor_get(v___x_6079_, 4);
                v_newLocalDecls_6085_ = leanh::lean_ctor_get(v___x_6079_, 5);
                v_newLocalDeclsForMVars_6086_ = leanh::lean_ctor_get(v___x_6079_, 6);
                v_newLetDecls_6087_ = leanh::lean_ctor_get(v___x_6079_, 7);
                v_nextExprIdx_6088_ = leanh::lean_ctor_get(v___x_6079_, 8);
                v_exprMVarArgs_6089_ = leanh::lean_ctor_get(v___x_6079_, 9);
                v_exprFVarArgs_6090_ = leanh::lean_ctor_get(v___x_6079_, 10);
                v_toProcess_6091_ = leanh::lean_ctor_get(v___x_6079_, 11);
                v_isSharedCheck_6109_ = (!leanh::lean_is_exclusive(v___x_6079_)) as u8;
                if v_isSharedCheck_6109_ == 0 {
                    v___x_6093_ = v___x_6079_;
                    v_isShared_6094_ = v_isSharedCheck_6109_;
                    state = 38;
                    continue;
                } else {
                    leanh::lean_inc(v_toProcess_6091_);
                    leanh::lean_inc(v_exprFVarArgs_6090_);
                    leanh::lean_inc(v_exprMVarArgs_6089_);
                    leanh::lean_inc(v_nextExprIdx_6088_);
                    leanh::lean_inc(v_newLetDecls_6087_);
                    leanh::lean_inc(v_newLocalDeclsForMVars_6086_);
                    leanh::lean_inc(v_newLocalDecls_6085_);
                    leanh::lean_inc(v_levelArgs_6084_);
                    leanh::lean_inc(v_nextLevelIdx_6083_);
                    leanh::lean_inc(v_levelParams_6082_);
                    leanh::lean_inc(v_visitedExpr_6081_);
                    leanh::lean_inc(v_visitedLevel_6080_);
                    leanh::lean_dec(v___x_6079_);
                    v___x_6093_ = leanh::lean_box(0);
                    v_isShared_6094_ = v_isSharedCheck_6109_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_6095_ = leanh::lean_unsigned_to_nat(0);
                v___x_6096_ = 0;
                v___x_6097_ = 0;
                leanh::lean_inc(v_a_6070_);
                v___x_6098_ = leanh::lean_alloc_ctor(0, 4, (2) as u32);
                leanh::lean_ctor_set(v___x_6098_, 0, v___x_6095_);
                leanh::lean_ctor_set(v___x_6098_, 1, v_a_6070_);
                leanh::lean_ctor_set(v___x_6098_, 2, v_a_6072_);
                leanh::lean_ctor_set(v___x_6098_, 3, v_a_6068_);
                leanh::lean_ctor_set_uint8(
                    v___x_6098_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___x_6096_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6098_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
                    v___x_6097_,
                );
                v___x_6099_ = lean_array_push(v_newLocalDeclsForMVars_6086_, v___x_6098_);
                v___x_6100_ = lean_array_push(v_exprMVarArgs_6089_, v_e_x27_6077_);
                if v_isShared_6094_ == 0 {
                    leanh::lean_ctor_set(v___x_6093_, 9, v___x_6100_);
                    leanh::lean_ctor_set(v___x_6093_, 6, v___x_6099_);
                    v___x_6102_ = v___x_6093_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_6108_ = leanh::lean_alloc_ctor(0, 12, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6108_, 0, v_visitedLevel_6080_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6108_, 1, v_visitedExpr_6081_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6108_, 2, v_levelParams_6082_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6108_, 3, v_nextLevelIdx_6083_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6108_, 4, v_levelArgs_6084_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6108_, 5, v_newLocalDecls_6085_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6108_, 6, v___x_6099_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6108_, 7, v_newLetDecls_6087_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6108_, 8, v_nextExprIdx_6088_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6108_, 9, v___x_6100_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6108_, 10, v_exprFVarArgs_6090_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6108_, 11, v_toProcess_6091_);
                    v___x_6102_ = v_reuseFailAlloc_6108_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                v___x_6103_ = lean_st_ref_set(v___y_6078_, v___x_6102_);
                v___x_6104_ = l_Lean_mkFVar(v_a_6070_);
                if v_isShared_6075_ == 0 {
                    leanh::lean_ctor_set(v___x_6074_, 0, v___x_6104_);
                    v___x_6106_ = v___x_6074_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_6107_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6107_, 0, v___x_6104_);
                    v___x_6106_ = v_reuseFailAlloc_6107_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_6106_;
            }
            41 => {
                v_fvars_6116_ = leanh::lean_ctor_get(v_val_6112_, 0);
                leanh::lean_inc_ref(v_fvars_6116_);
                leanh::lean_dec(v_val_6112_);
                v___f_6117_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Closure_collectExprAux___lam__1___boxed as *mut core::ffi::c_void,
                    10,
                    1,
                );
                leanh::lean_closure_set(v___f_6117_, 0, v_e_5840_);
                v___x_6118_ = lean_array_get_size(v_fvars_6116_);
                leanh::lean_dec_ref(v_fvars_6116_);
                if v_isShared_6115_ == 0 {
                    leanh::lean_ctor_set(v___x_6114_, 0, v___x_6118_);
                    v___x_6120_ = v___x_6114_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_6124_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6124_, 0, v___x_6118_);
                    v___x_6120_ = v_reuseFailAlloc_6124_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                v___x_6121_ = 0;
                v___x_6122_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_6064_, v___x_6120_, v___f_6117_, v___x_6121_, v___x_6121_, v_a_5841_, v_a_5842_, v_a_5843_, v_a_5844_, v_a_5845_, v_a_5846_);
                if leanh::lean_obj_tag(v___x_6122_) == 0 {
                    v_a_6123_ = leanh::lean_ctor_get(v___x_6122_, 0);
                    leanh::lean_inc(v_a_6123_);
                    leanh::lean_dec_ref_known(v___x_6122_, 1);
                    v_e_x27_6077_ = v_a_6123_;
                    v___y_6078_ = v_a_5842_;
                    state = 37;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_6074_);
                    leanh::lean_dec(v_a_6072_);
                    leanh::lean_dec(v_a_6070_);
                    leanh::lean_dec(v_a_6068_);
                    return v___x_6122_;
                }
            }
            43 => {
                if v_isShared_6129_ == 0 {
                    v___x_6131_ = v___x_6128_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_6132_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6132_, 0, v_a_6126_);
                    v___x_6131_ = v_reuseFailAlloc_6132_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_6131_;
            }
            45 => {
                if v_isShared_6138_ == 0 {
                    v___x_6140_ = v___x_6137_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_6141_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6141_, 0, v_a_6135_);
                    v___x_6140_ = v_reuseFailAlloc_6141_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_6140_;
            }
            47 => {
                if v_isShared_6146_ == 0 {
                    v___x_6148_ = v___x_6145_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_6149_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6149_, 0, v_a_6143_);
                    v___x_6148_ = v_reuseFailAlloc_6149_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_6148_;
            }
            49 => {
                if v_isShared_6154_ == 0 {
                    v___x_6156_ = v___x_6153_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_6157_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6157_, 0, v_a_6151_);
                    v___x_6156_ = v_reuseFailAlloc_6157_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_6156_;
            }
            51 => {
                v___x_6170_ =
                    l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(
                        v___y_6164_,
                        v___y_6165_,
                        v___y_6166_,
                        v___y_6167_,
                        v___y_6168_,
                        v___y_6169_,
                    );
                if leanh::lean_obj_tag(v___x_6170_) == 0 {
                    v_a_6171_ = leanh::lean_ctor_get(v___x_6170_, 0);
                    leanh::lean_inc_n(v_a_6171_, 2);
                    leanh::lean_dec_ref_known(v___x_6170_, 1);
                    v___x_6172_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6172_, 0, v_fvarId_6159_);
                    leanh::lean_ctor_set(v___x_6172_, 1, v_a_6171_);
                    v___x_6173_ =
                        l_Lean_Meta_Closure_pushToProcess___redArg(v___x_6172_, v___y_6165_);
                    if leanh::lean_obj_tag(v___x_6173_) == 0 {
                        v_isSharedCheck_6181_ =
                            (!leanh::lean_is_exclusive(v___x_6173_)) as u8;
                        if v_isSharedCheck_6181_ == 0 {
                            v_unused_6182_ = leanh::lean_ctor_get(v___x_6173_, 0);
                            leanh::lean_dec(v_unused_6182_);
                            v___x_6175_ = v___x_6173_;
                            v_isShared_6176_ = v_isSharedCheck_6181_;
                            state = 52;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_6173_);
                            v___x_6175_ = leanh::lean_box(0);
                            v_isShared_6176_ = v_isSharedCheck_6181_;
                            state = 52;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_6171_);
                        v_a_6183_ = leanh::lean_ctor_get(v___x_6173_, 0);
                        v_isSharedCheck_6190_ =
                            (!leanh::lean_is_exclusive(v___x_6173_)) as u8;
                        if v_isSharedCheck_6190_ == 0 {
                            v___x_6185_ = v___x_6173_;
                            v_isShared_6186_ = v_isSharedCheck_6190_;
                            state = 54;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6183_);
                            leanh::lean_dec(v___x_6173_);
                            v___x_6185_ = leanh::lean_box(0);
                            v_isShared_6186_ = v_isSharedCheck_6190_;
                            state = 54;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_fvarId_6159_);
                    v_a_6191_ = leanh::lean_ctor_get(v___x_6170_, 0);
                    v_isSharedCheck_6198_ = (!leanh::lean_is_exclusive(v___x_6170_)) as u8;
                    if v_isSharedCheck_6198_ == 0 {
                        v___x_6193_ = v___x_6170_;
                        v_isShared_6194_ = v_isSharedCheck_6198_;
                        state = 56;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6191_);
                        leanh::lean_dec(v___x_6170_);
                        v___x_6193_ = leanh::lean_box(0);
                        v_isShared_6194_ = v_isSharedCheck_6198_;
                        state = 56;
                        continue;
                    }
                }
            }
            52 => {
                v___x_6177_ = l_Lean_mkFVar(v_a_6171_);
                if v_isShared_6176_ == 0 {
                    leanh::lean_ctor_set(v___x_6175_, 0, v___x_6177_);
                    v___x_6179_ = v___x_6175_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_6180_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6180_, 0, v___x_6177_);
                    v___x_6179_ = v_reuseFailAlloc_6180_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                return v___x_6179_;
            }
            54 => {
                if v_isShared_6186_ == 0 {
                    v___x_6188_ = v___x_6185_;
                    state = 55;
                    continue;
                } else {
                    v_reuseFailAlloc_6189_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6189_, 0, v_a_6183_);
                    v___x_6188_ = v_reuseFailAlloc_6189_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                return v___x_6188_;
            }
            56 => {
                if v_isShared_6194_ == 0 {
                    v___x_6196_ = v___x_6193_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_6197_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6197_, 0, v_a_6191_);
                    v___x_6196_ = v_reuseFailAlloc_6197_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                return v___x_6196_;
            }
            58 => {
                if v_isShared_6206_ == 0 {
                    v___x_6208_ = v___x_6205_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_6209_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6209_, 0, v_a_6203_);
                    v___x_6208_ = v_reuseFailAlloc_6209_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                return v___x_6208_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Closure_collectExprAux___lam__0(
    mut v_e_6212_: *mut leanh::LeanObject,
    mut v___y_6213_: u8,
    mut v___y_6214_: *mut leanh::LeanObject,
    mut v___y_6215_: *mut leanh::LeanObject,
    mut v___y_6216_: *mut leanh::LeanObject,
    mut v___y_6217_: *mut leanh::LeanObject,
    mut v___y_6218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_6222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6228_: u8 = 0;
    let mut v___x_6229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_6230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_6231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_6232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextLevelIdx_6233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelArgs_6234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDecls_6235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDeclsForMVars_6236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLetDecls_6237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextExprIdx_6238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprMVarArgs_6239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprFVarArgs_6240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toProcess_6241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6244_: u8 = 0;
    let mut v___x_6245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6253_: u8 = 0;
    let mut v_isSharedCheck_6254_: u8 = 0;
    let mut v_val_6255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6258_: u8 = 0;
    let mut v___x_6260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6262_: u8 = 0;
    let mut v___x_6263_: u8 = 0;
    let mut v___x_6264_: u8 = 0;
    let mut v___x_6265_: u8 = 0;
    let mut v___x_6266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6263_ = l_Lean_Expr_hasLevelParam(v_e_6212_);
                if v___x_6263_ == 0 {
                    v___x_6264_ = l_Lean_Expr_hasFVar(v_e_6212_);
                    if v___x_6264_ == 0 {
                        v___x_6265_ = l_Lean_Expr_hasMVar(v_e_6212_);
                        if v___x_6265_ == 0 {
                            v___x_6266_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_6266_, 0, v_e_6212_);
                            return v___x_6266_;
                        } else {
                            state = 1;
                            continue;
                        }
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
                v___x_6221_ = lean_st_ref_get(v___y_6214_);
                v_visitedExpr_6222_ = leanh::lean_ctor_get(v___x_6221_, 1);
                leanh::lean_inc_ref(v_visitedExpr_6222_);
                leanh::lean_dec(v___x_6221_);
                v___x_6223_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_visitedExpr_6222_, v_e_6212_);
                leanh::lean_dec_ref(v_visitedExpr_6222_);
                if leanh::lean_obj_tag(v___x_6223_) == 0 {
                    leanh::lean_inc_ref(v_e_6212_);
                    v___x_6224_ = l_Lean_Meta_Closure_collectExprAux(
                        v_e_6212_,
                        v___y_6213_,
                        v___y_6214_,
                        v___y_6215_,
                        v___y_6216_,
                        v___y_6217_,
                        v___y_6218_,
                    );
                    if leanh::lean_obj_tag(v___x_6224_) == 0 {
                        v_a_6225_ = leanh::lean_ctor_get(v___x_6224_, 0);
                        v_isSharedCheck_6254_ =
                            (!leanh::lean_is_exclusive(v___x_6224_)) as u8;
                        if v_isSharedCheck_6254_ == 0 {
                            v___x_6227_ = v___x_6224_;
                            v_isShared_6228_ = v_isSharedCheck_6254_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6225_);
                            leanh::lean_dec(v___x_6224_);
                            v___x_6227_ = leanh::lean_box(0);
                            v_isShared_6228_ = v_isSharedCheck_6254_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_6212_);
                        return v___x_6224_;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_6212_);
                    v_val_6255_ = leanh::lean_ctor_get(v___x_6223_, 0);
                    v_isSharedCheck_6262_ = (!leanh::lean_is_exclusive(v___x_6223_)) as u8;
                    if v_isSharedCheck_6262_ == 0 {
                        v___x_6257_ = v___x_6223_;
                        v_isShared_6258_ = v_isSharedCheck_6262_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6255_);
                        leanh::lean_dec(v___x_6223_);
                        v___x_6257_ = leanh::lean_box(0);
                        v_isShared_6258_ = v_isSharedCheck_6262_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6229_ = lean_st_ref_take(v___y_6214_);
                v_visitedLevel_6230_ = leanh::lean_ctor_get(v___x_6229_, 0);
                v_visitedExpr_6231_ = leanh::lean_ctor_get(v___x_6229_, 1);
                v_levelParams_6232_ = leanh::lean_ctor_get(v___x_6229_, 2);
                v_nextLevelIdx_6233_ = leanh::lean_ctor_get(v___x_6229_, 3);
                v_levelArgs_6234_ = leanh::lean_ctor_get(v___x_6229_, 4);
                v_newLocalDecls_6235_ = leanh::lean_ctor_get(v___x_6229_, 5);
                v_newLocalDeclsForMVars_6236_ = leanh::lean_ctor_get(v___x_6229_, 6);
                v_newLetDecls_6237_ = leanh::lean_ctor_get(v___x_6229_, 7);
                v_nextExprIdx_6238_ = leanh::lean_ctor_get(v___x_6229_, 8);
                v_exprMVarArgs_6239_ = leanh::lean_ctor_get(v___x_6229_, 9);
                v_exprFVarArgs_6240_ = leanh::lean_ctor_get(v___x_6229_, 10);
                v_toProcess_6241_ = leanh::lean_ctor_get(v___x_6229_, 11);
                v_isSharedCheck_6253_ = (!leanh::lean_is_exclusive(v___x_6229_)) as u8;
                if v_isSharedCheck_6253_ == 0 {
                    v___x_6243_ = v___x_6229_;
                    v_isShared_6244_ = v_isSharedCheck_6253_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_toProcess_6241_);
                    leanh::lean_inc(v_exprFVarArgs_6240_);
                    leanh::lean_inc(v_exprMVarArgs_6239_);
                    leanh::lean_inc(v_nextExprIdx_6238_);
                    leanh::lean_inc(v_newLetDecls_6237_);
                    leanh::lean_inc(v_newLocalDeclsForMVars_6236_);
                    leanh::lean_inc(v_newLocalDecls_6235_);
                    leanh::lean_inc(v_levelArgs_6234_);
                    leanh::lean_inc(v_nextLevelIdx_6233_);
                    leanh::lean_inc(v_levelParams_6232_);
                    leanh::lean_inc(v_visitedExpr_6231_);
                    leanh::lean_inc(v_visitedLevel_6230_);
                    leanh::lean_dec(v___x_6229_);
                    v___x_6243_ = leanh::lean_box(0);
                    v_isShared_6244_ = v_isSharedCheck_6253_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc(v_a_6225_);
                v___x_6245_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_visitedExpr_6231_, v_e_6212_, v_a_6225_);
                if v_isShared_6244_ == 0 {
                    leanh::lean_ctor_set(v___x_6243_, 1, v___x_6245_);
                    v___x_6247_ = v___x_6243_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6252_ = leanh::lean_alloc_ctor(0, 12, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6252_, 0, v_visitedLevel_6230_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6252_, 1, v___x_6245_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6252_, 2, v_levelParams_6232_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6252_, 3, v_nextLevelIdx_6233_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6252_, 4, v_levelArgs_6234_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6252_, 5, v_newLocalDecls_6235_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_6252_,
                        6,
                        v_newLocalDeclsForMVars_6236_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_6252_, 7, v_newLetDecls_6237_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6252_, 8, v_nextExprIdx_6238_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6252_, 9, v_exprMVarArgs_6239_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6252_, 10, v_exprFVarArgs_6240_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6252_, 11, v_toProcess_6241_);
                    v___x_6247_ = v_reuseFailAlloc_6252_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6248_ = lean_st_ref_set(v___y_6214_, v___x_6247_);
                if v_isShared_6228_ == 0 {
                    v___x_6250_ = v___x_6227_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6251_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6251_, 0, v_a_6225_);
                    v___x_6250_ = v_reuseFailAlloc_6251_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6250_;
            }
            6 => {
                if v_isShared_6258_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6257_, 0);
                    v___x_6260_ = v___x_6257_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6261_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6261_, 0, v_val_6255_);
                    v___x_6260_ = v_reuseFailAlloc_6261_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6260_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Closure_collectExprAux___lam__0___boxed(
    mut v_e_6267_: *mut leanh::LeanObject,
    mut v___y_6268_: *mut leanh::LeanObject,
    mut v___y_6269_: *mut leanh::LeanObject,
    mut v___y_6270_: *mut leanh::LeanObject,
    mut v___y_6271_: *mut leanh::LeanObject,
    mut v___y_6272_: *mut leanh::LeanObject,
    mut v___y_6273_: *mut leanh::LeanObject,
    mut v___y_6274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_18416__boxed_6275_: u8 = 0;
    let mut v_res_6276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_18416__boxed_6275_ = (leanh::lean_unbox(v___y_6268_) as u8);
    v_res_6276_ = l_Lean_Meta_Closure_collectExprAux___lam__0(
        v_e_6267_,
        v___y_18416__boxed_6275_,
        v___y_6269_,
        v___y_6270_,
        v___y_6271_,
        v___y_6272_,
        v___y_6273_,
    );
    leanh::lean_dec(v___y_6273_);
    leanh::lean_dec_ref(v___y_6272_);
    leanh::lean_dec(v___y_6271_);
    leanh::lean_dec_ref(v___y_6270_);
    leanh::lean_dec(v___y_6269_);
    return v_res_6276_;
}
pub unsafe fn l_Lean_Meta_Closure_collectExprAux___boxed(
    mut v_e_6277_: *mut leanh::LeanObject,
    mut v_a_6278_: *mut leanh::LeanObject,
    mut v_a_6279_: *mut leanh::LeanObject,
    mut v_a_6280_: *mut leanh::LeanObject,
    mut v_a_6281_: *mut leanh::LeanObject,
    mut v_a_6282_: *mut leanh::LeanObject,
    mut v_a_6283_: *mut leanh::LeanObject,
    mut v_a_6284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_6285_: u8 = 0;
    let mut v_res_6286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_6285_ = (leanh::lean_unbox(v_a_6278_) as u8);
    v_res_6286_ = l_Lean_Meta_Closure_collectExprAux(
        v_e_6277_,
        v_a_boxed_6285_,
        v_a_6279_,
        v_a_6280_,
        v_a_6281_,
        v_a_6282_,
        v_a_6283_,
    );
    leanh::lean_dec(v_a_6283_);
    leanh::lean_dec_ref(v_a_6282_);
    leanh::lean_dec(v_a_6281_);
    leanh::lean_dec_ref(v_a_6280_);
    leanh::lean_dec(v_a_6279_);
    return v_res_6286_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0(
    mut v_00_u03b2_6287_: *mut leanh::LeanObject,
    mut v_m_6288_: *mut leanh::LeanObject,
    mut v_a_6289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6290_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_m_6288_, v_a_6289_);
    return v___x_6290_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___boxed(
    mut v_00_u03b2_6291_: *mut leanh::LeanObject,
    mut v_m_6292_: *mut leanh::LeanObject,
    mut v_a_6293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6294_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0(v_00_u03b2_6291_, v_m_6292_, v_a_6293_);
    leanh::lean_dec_ref(v_a_6293_);
    leanh::lean_dec_ref(v_m_6292_);
    return v_res_6294_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1(
    mut v_00_u03b2_6295_: *mut leanh::LeanObject,
    mut v_m_6296_: *mut leanh::LeanObject,
    mut v_a_6297_: *mut leanh::LeanObject,
    mut v_b_6298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6299_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_m_6296_, v_a_6297_, v_b_6298_);
    return v___x_6299_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2(
    mut v_x_6300_: *mut leanh::LeanObject,
    mut v_x_6301_: *mut leanh::LeanObject,
    mut v___y_6302_: u8,
    mut v___y_6303_: *mut leanh::LeanObject,
    mut v___y_6304_: *mut leanh::LeanObject,
    mut v___y_6305_: *mut leanh::LeanObject,
    mut v___y_6306_: *mut leanh::LeanObject,
    mut v___y_6307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6309_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(
        v_x_6300_,
        v_x_6301_,
        v___y_6303_,
    );
    return v___x_6309_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___boxed(
    mut v_x_6310_: *mut leanh::LeanObject,
    mut v_x_6311_: *mut leanh::LeanObject,
    mut v___y_6312_: *mut leanh::LeanObject,
    mut v___y_6313_: *mut leanh::LeanObject,
    mut v___y_6314_: *mut leanh::LeanObject,
    mut v___y_6315_: *mut leanh::LeanObject,
    mut v___y_6316_: *mut leanh::LeanObject,
    mut v___y_6317_: *mut leanh::LeanObject,
    mut v___y_6318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_19232__boxed_6319_: u8 = 0;
    let mut v_res_6320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_19232__boxed_6319_ = (leanh::lean_unbox(v___y_6312_) as u8);
    v_res_6320_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2(
        v_x_6310_,
        v_x_6311_,
        v___y_19232__boxed_6319_,
        v___y_6313_,
        v___y_6314_,
        v___y_6315_,
        v___y_6316_,
        v___y_6317_,
    );
    leanh::lean_dec(v___y_6317_);
    leanh::lean_dec_ref(v___y_6316_);
    leanh::lean_dec(v___y_6315_);
    leanh::lean_dec_ref(v___y_6314_);
    leanh::lean_dec(v___y_6313_);
    return v_res_6320_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7(
    mut v___y_6321_: u8,
    mut v___y_6322_: *mut leanh::LeanObject,
    mut v___y_6323_: *mut leanh::LeanObject,
    mut v___y_6324_: *mut leanh::LeanObject,
    mut v___y_6325_: *mut leanh::LeanObject,
    mut v___y_6326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6328_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_6326_);
    return v___x_6328_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___boxed(
    mut v___y_6329_: *mut leanh::LeanObject,
    mut v___y_6330_: *mut leanh::LeanObject,
    mut v___y_6331_: *mut leanh::LeanObject,
    mut v___y_6332_: *mut leanh::LeanObject,
    mut v___y_6333_: *mut leanh::LeanObject,
    mut v___y_6334_: *mut leanh::LeanObject,
    mut v___y_6335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_19259__boxed_6336_: u8 = 0;
    let mut v_res_6337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_19259__boxed_6336_ = (leanh::lean_unbox(v___y_6329_) as u8);
    v_res_6337_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7(v___y_19259__boxed_6336_, v___y_6330_, v___y_6331_, v___y_6332_, v___y_6333_, v___y_6334_);
    leanh::lean_dec(v___y_6334_);
    leanh::lean_dec_ref(v___y_6333_);
    leanh::lean_dec(v___y_6332_);
    leanh::lean_dec_ref(v___y_6331_);
    leanh::lean_dec(v___y_6330_);
    return v_res_6337_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0(
    mut v_00_u03b2_6338_: *mut leanh::LeanObject,
    mut v_a_6339_: *mut leanh::LeanObject,
    mut v_x_6340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6341_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_6339_, v_x_6340_);
    return v___x_6341_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___boxed(
    mut v_00_u03b2_6342_: *mut leanh::LeanObject,
    mut v_a_6343_: *mut leanh::LeanObject,
    mut v_x_6344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6345_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0(v_00_u03b2_6342_, v_a_6343_, v_x_6344_);
    leanh::lean_dec(v_x_6344_);
    leanh::lean_dec_ref(v_a_6343_);
    return v_res_6345_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2(
    mut v_00_u03b2_6346_: *mut leanh::LeanObject,
    mut v_a_6347_: *mut leanh::LeanObject,
    mut v_x_6348_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6349_: u8 = 0;
    v___x_6349_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_6347_, v_x_6348_);
    return v___x_6349_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___boxed(
    mut v_00_u03b2_6350_: *mut leanh::LeanObject,
    mut v_a_6351_: *mut leanh::LeanObject,
    mut v_x_6352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6353_: u8 = 0;
    let mut v_r_6354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6353_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2(v_00_u03b2_6350_, v_a_6351_, v_x_6352_);
    leanh::lean_dec(v_x_6352_);
    leanh::lean_dec_ref(v_a_6351_);
    v_r_6354_ = leanh::lean_box((v_res_6353_) as usize);
    return v_r_6354_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3(
    mut v_00_u03b2_6355_: *mut leanh::LeanObject,
    mut v_data_6356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6357_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(v_data_6356_);
    return v___x_6357_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4(
    mut v_00_u03b2_6358_: *mut leanh::LeanObject,
    mut v_a_6359_: *mut leanh::LeanObject,
    mut v_b_6360_: *mut leanh::LeanObject,
    mut v_x_6361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6362_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_6359_, v_b_6360_, v_x_6361_);
    return v___x_6362_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6(
    mut v_00_u03b2_6363_: *mut leanh::LeanObject,
    mut v_i_6364_: *mut leanh::LeanObject,
    mut v_source_6365_: *mut leanh::LeanObject,
    mut v_target_6366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6367_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(v_i_6364_, v_source_6365_, v_target_6366_);
    return v___x_6367_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10(
    mut v_00_u03b2_6368_: *mut leanh::LeanObject,
    mut v_x_6369_: *mut leanh::LeanObject,
    mut v_x_6370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6371_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(v_x_6369_, v_x_6370_);
    return v___x_6371_;
}
pub unsafe fn l_Lean_Meta_Closure_collectExpr(
    mut v_e_6372_: *mut leanh::LeanObject,
    mut v_a_6373_: u8,
    mut v_a_6374_: *mut leanh::LeanObject,
    mut v_a_6375_: *mut leanh::LeanObject,
    mut v_a_6376_: *mut leanh::LeanObject,
    mut v_a_6377_: *mut leanh::LeanObject,
    mut v_a_6378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_6384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6390_: u8 = 0;
    let mut v___x_6391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_6392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_6393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_6394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextLevelIdx_6395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelArgs_6396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDecls_6397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDeclsForMVars_6398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLetDecls_6399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextExprIdx_6400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprMVarArgs_6401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprFVarArgs_6402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toProcess_6403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6406_: u8 = 0;
    let mut v___x_6407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6415_: u8 = 0;
    let mut v_isSharedCheck_6416_: u8 = 0;
    let mut v_val_6417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6420_: u8 = 0;
    let mut v___x_6422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6424_: u8 = 0;
    let mut v___x_6425_: u8 = 0;
    let mut v___x_6426_: u8 = 0;
    let mut v___x_6427_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6380_ = l_Lean_Meta_Closure_preprocess(
                    v_e_6372_, v_a_6373_, v_a_6374_, v_a_6375_, v_a_6376_, v_a_6377_, v_a_6378_,
                );
                if leanh::lean_obj_tag(v___x_6380_) == 0 {
                    v_a_6381_ = leanh::lean_ctor_get(v___x_6380_, 0);
                    leanh::lean_inc(v_a_6381_);
                    v___x_6425_ = l_Lean_Expr_hasLevelParam(v_a_6381_);
                    if v___x_6425_ == 0 {
                        v___x_6426_ = l_Lean_Expr_hasFVar(v_a_6381_);
                        if v___x_6426_ == 0 {
                            v___x_6427_ = l_Lean_Expr_hasMVar(v_a_6381_);
                            if v___x_6427_ == 0 {
                                leanh::lean_dec(v_a_6381_);
                                return v___x_6380_;
                            } else {
                                leanh::lean_dec_ref_known(v___x_6380_, 1);
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v___x_6380_, 1);
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_6380_, 1);
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_6380_;
                }
            }
            1 => {
                v___x_6383_ = lean_st_ref_get(v_a_6374_);
                v_visitedExpr_6384_ = leanh::lean_ctor_get(v___x_6383_, 1);
                leanh::lean_inc_ref(v_visitedExpr_6384_);
                leanh::lean_dec(v___x_6383_);
                v___x_6385_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_visitedExpr_6384_, v_a_6381_);
                leanh::lean_dec_ref(v_visitedExpr_6384_);
                if leanh::lean_obj_tag(v___x_6385_) == 0 {
                    leanh::lean_inc(v_a_6381_);
                    v___x_6386_ = l_Lean_Meta_Closure_collectExprAux(
                        v_a_6381_, v_a_6373_, v_a_6374_, v_a_6375_, v_a_6376_, v_a_6377_, v_a_6378_,
                    );
                    if leanh::lean_obj_tag(v___x_6386_) == 0 {
                        v_a_6387_ = leanh::lean_ctor_get(v___x_6386_, 0);
                        v_isSharedCheck_6416_ =
                            (!leanh::lean_is_exclusive(v___x_6386_)) as u8;
                        if v_isSharedCheck_6416_ == 0 {
                            v___x_6389_ = v___x_6386_;
                            v_isShared_6390_ = v_isSharedCheck_6416_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6387_);
                            leanh::lean_dec(v___x_6386_);
                            v___x_6389_ = leanh::lean_box(0);
                            v_isShared_6390_ = v_isSharedCheck_6416_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_6381_);
                        return v___x_6386_;
                    }
                } else {
                    leanh::lean_dec(v_a_6381_);
                    v_val_6417_ = leanh::lean_ctor_get(v___x_6385_, 0);
                    v_isSharedCheck_6424_ = (!leanh::lean_is_exclusive(v___x_6385_)) as u8;
                    if v_isSharedCheck_6424_ == 0 {
                        v___x_6419_ = v___x_6385_;
                        v_isShared_6420_ = v_isSharedCheck_6424_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6417_);
                        leanh::lean_dec(v___x_6385_);
                        v___x_6419_ = leanh::lean_box(0);
                        v_isShared_6420_ = v_isSharedCheck_6424_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6391_ = lean_st_ref_take(v_a_6374_);
                v_visitedLevel_6392_ = leanh::lean_ctor_get(v___x_6391_, 0);
                v_visitedExpr_6393_ = leanh::lean_ctor_get(v___x_6391_, 1);
                v_levelParams_6394_ = leanh::lean_ctor_get(v___x_6391_, 2);
                v_nextLevelIdx_6395_ = leanh::lean_ctor_get(v___x_6391_, 3);
                v_levelArgs_6396_ = leanh::lean_ctor_get(v___x_6391_, 4);
                v_newLocalDecls_6397_ = leanh::lean_ctor_get(v___x_6391_, 5);
                v_newLocalDeclsForMVars_6398_ = leanh::lean_ctor_get(v___x_6391_, 6);
                v_newLetDecls_6399_ = leanh::lean_ctor_get(v___x_6391_, 7);
                v_nextExprIdx_6400_ = leanh::lean_ctor_get(v___x_6391_, 8);
                v_exprMVarArgs_6401_ = leanh::lean_ctor_get(v___x_6391_, 9);
                v_exprFVarArgs_6402_ = leanh::lean_ctor_get(v___x_6391_, 10);
                v_toProcess_6403_ = leanh::lean_ctor_get(v___x_6391_, 11);
                v_isSharedCheck_6415_ = (!leanh::lean_is_exclusive(v___x_6391_)) as u8;
                if v_isSharedCheck_6415_ == 0 {
                    v___x_6405_ = v___x_6391_;
                    v_isShared_6406_ = v_isSharedCheck_6415_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_toProcess_6403_);
                    leanh::lean_inc(v_exprFVarArgs_6402_);
                    leanh::lean_inc(v_exprMVarArgs_6401_);
                    leanh::lean_inc(v_nextExprIdx_6400_);
                    leanh::lean_inc(v_newLetDecls_6399_);
                    leanh::lean_inc(v_newLocalDeclsForMVars_6398_);
                    leanh::lean_inc(v_newLocalDecls_6397_);
                    leanh::lean_inc(v_levelArgs_6396_);
                    leanh::lean_inc(v_nextLevelIdx_6395_);
                    leanh::lean_inc(v_levelParams_6394_);
                    leanh::lean_inc(v_visitedExpr_6393_);
                    leanh::lean_inc(v_visitedLevel_6392_);
                    leanh::lean_dec(v___x_6391_);
                    v___x_6405_ = leanh::lean_box(0);
                    v_isShared_6406_ = v_isSharedCheck_6415_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc(v_a_6387_);
                v___x_6407_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_visitedExpr_6393_, v_a_6381_, v_a_6387_);
                if v_isShared_6406_ == 0 {
                    leanh::lean_ctor_set(v___x_6405_, 1, v___x_6407_);
                    v___x_6409_ = v___x_6405_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6414_ = leanh::lean_alloc_ctor(0, 12, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6414_, 0, v_visitedLevel_6392_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6414_, 1, v___x_6407_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6414_, 2, v_levelParams_6394_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6414_, 3, v_nextLevelIdx_6395_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6414_, 4, v_levelArgs_6396_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6414_, 5, v_newLocalDecls_6397_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_6414_,
                        6,
                        v_newLocalDeclsForMVars_6398_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_6414_, 7, v_newLetDecls_6399_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6414_, 8, v_nextExprIdx_6400_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6414_, 9, v_exprMVarArgs_6401_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6414_, 10, v_exprFVarArgs_6402_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6414_, 11, v_toProcess_6403_);
                    v___x_6409_ = v_reuseFailAlloc_6414_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6410_ = lean_st_ref_set(v_a_6374_, v___x_6409_);
                if v_isShared_6390_ == 0 {
                    v___x_6412_ = v___x_6389_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6413_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6413_, 0, v_a_6387_);
                    v___x_6412_ = v_reuseFailAlloc_6413_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6412_;
            }
            6 => {
                if v_isShared_6420_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6419_, 0);
                    v___x_6422_ = v___x_6419_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6423_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6423_, 0, v_val_6417_);
                    v___x_6422_ = v_reuseFailAlloc_6423_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6422_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Closure_collectExpr___boxed(
    mut v_e_6428_: *mut leanh::LeanObject,
    mut v_a_6429_: *mut leanh::LeanObject,
    mut v_a_6430_: *mut leanh::LeanObject,
    mut v_a_6431_: *mut leanh::LeanObject,
    mut v_a_6432_: *mut leanh::LeanObject,
    mut v_a_6433_: *mut leanh::LeanObject,
    mut v_a_6434_: *mut leanh::LeanObject,
    mut v_a_6435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_6436_: u8 = 0;
    let mut v_res_6437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_6436_ = (leanh::lean_unbox(v_a_6429_) as u8);
    v_res_6437_ = l_Lean_Meta_Closure_collectExpr(
        v_e_6428_,
        v_a_boxed_6436_,
        v_a_6430_,
        v_a_6431_,
        v_a_6432_,
        v_a_6433_,
        v_a_6434_,
    );
    leanh::lean_dec(v_a_6434_);
    leanh::lean_dec_ref(v_a_6433_);
    leanh::lean_dec(v_a_6432_);
    leanh::lean_dec_ref(v_a_6431_);
    leanh::lean_dec(v_a_6430_);
    return v_res_6437_;
}
pub unsafe fn l_Lean_Meta_Closure_pickNextToProcessAux(
    mut v_lctx_6438_: *mut leanh::LeanObject,
    mut v_i_6439_: *mut leanh::LeanObject,
    mut v_toProcess_6440_: *mut leanh::LeanObject,
    mut v_elem_6441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6443_: u8 = 0;
    let mut v___x_6444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_elem_x27_6446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6452_: u8 = 0;
    let mut v___x_6453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6442_ = lean_array_get_size(v_toProcess_6440_);
                v___x_6443_ = lean_nat_dec_lt(v_i_6439_, v___x_6442_);
                if v___x_6443_ == 0 {
                    leanh::lean_dec(v_i_6439_);
                    leanh::lean_dec_ref(v_lctx_6438_);
                    v___x_6444_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6444_, 0, v_elem_6441_);
                    leanh::lean_ctor_set(v___x_6444_, 1, v_toProcess_6440_);
                    return v___x_6444_;
                } else {
                    v_fvarId_6445_ = leanh::lean_ctor_get(v_elem_6441_, 0);
                    v_elem_x27_6446_ = lean_array_fget_borrowed(v_toProcess_6440_, v_i_6439_);
                    v_fvarId_6447_ = leanh::lean_ctor_get(v_elem_x27_6446_, 0);
                    leanh::lean_inc(v_fvarId_6445_);
                    leanh::lean_inc_ref_n(v_lctx_6438_, 2);
                    v___x_6448_ = l_Lean_LocalContext_get_x21(v_lctx_6438_, v_fvarId_6445_);
                    v___x_6449_ = l_Lean_LocalDecl_index(v___x_6448_);
                    leanh::lean_dec_ref(v___x_6448_);
                    leanh::lean_inc(v_fvarId_6447_);
                    v___x_6450_ = l_Lean_LocalContext_get_x21(v_lctx_6438_, v_fvarId_6447_);
                    v___x_6451_ = l_Lean_LocalDecl_index(v___x_6450_);
                    leanh::lean_dec_ref(v___x_6450_);
                    v___x_6452_ = lean_nat_dec_lt(v___x_6449_, v___x_6451_);
                    leanh::lean_dec(v___x_6451_);
                    leanh::lean_dec(v___x_6449_);
                    if v___x_6452_ == 0 {
                        v___x_6453_ = leanh::lean_unsigned_to_nat(1);
                        v___x_6454_ = lean_nat_add(v_i_6439_, v___x_6453_);
                        leanh::lean_dec(v_i_6439_);
                        v_i_6439_ = v___x_6454_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_elem_x27_6446_);
                        v___x_6456_ = leanh::lean_unsigned_to_nat(1);
                        v___x_6457_ = lean_nat_add(v_i_6439_, v___x_6456_);
                        v___x_6458_ = lean_array_fset(v_toProcess_6440_, v_i_6439_, v_elem_6441_);
                        leanh::lean_dec(v_i_6439_);
                        v_i_6439_ = v___x_6457_;
                        v_toProcess_6440_ = v___x_6458_;
                        v_elem_6441_ = v_elem_x27_6446_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(
    mut v_a_6460_: *mut leanh::LeanObject,
    mut v_a_6461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toProcess_6464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6467_: u8 = 0;
    let mut v___x_6468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_6469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_6470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_6471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_6472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextLevelIdx_6473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelArgs_6474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDecls_6475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDeclsForMVars_6476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLetDecls_6477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextExprIdx_6478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprMVarArgs_6479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprFVarArgs_6480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toProcess_6481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6484_: u8 = 0;
    let mut v___x_6485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6500_: u8 = 0;
    let mut v___x_6501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6463_ = lean_st_ref_get(v_a_6460_);
                v_toProcess_6464_ = leanh::lean_ctor_get(v___x_6463_, 11);
                leanh::lean_inc_ref(v_toProcess_6464_);
                leanh::lean_dec(v___x_6463_);
                v___x_6465_ = lean_array_get_size(v_toProcess_6464_);
                leanh::lean_dec_ref(v_toProcess_6464_);
                v___x_6466_ = leanh::lean_unsigned_to_nat(0);
                v___x_6467_ = lean_nat_dec_eq(v___x_6465_, v___x_6466_);
                if v___x_6467_ == 0 {
                    v___x_6468_ = lean_st_ref_take(v_a_6460_);
                    v_lctx_6469_ = leanh::lean_ctor_get(v_a_6461_, 2);
                    v_visitedLevel_6470_ = leanh::lean_ctor_get(v___x_6468_, 0);
                    v_visitedExpr_6471_ = leanh::lean_ctor_get(v___x_6468_, 1);
                    v_levelParams_6472_ = leanh::lean_ctor_get(v___x_6468_, 2);
                    v_nextLevelIdx_6473_ = leanh::lean_ctor_get(v___x_6468_, 3);
                    v_levelArgs_6474_ = leanh::lean_ctor_get(v___x_6468_, 4);
                    v_newLocalDecls_6475_ = leanh::lean_ctor_get(v___x_6468_, 5);
                    v_newLocalDeclsForMVars_6476_ = leanh::lean_ctor_get(v___x_6468_, 6);
                    v_newLetDecls_6477_ = leanh::lean_ctor_get(v___x_6468_, 7);
                    v_nextExprIdx_6478_ = leanh::lean_ctor_get(v___x_6468_, 8);
                    v_exprMVarArgs_6479_ = leanh::lean_ctor_get(v___x_6468_, 9);
                    v_exprFVarArgs_6480_ = leanh::lean_ctor_get(v___x_6468_, 10);
                    v_toProcess_6481_ = leanh::lean_ctor_get(v___x_6468_, 11);
                    v_isSharedCheck_6500_ = (!leanh::lean_is_exclusive(v___x_6468_)) as u8;
                    if v_isSharedCheck_6500_ == 0 {
                        v___x_6483_ = v___x_6468_;
                        v_isShared_6484_ = v_isSharedCheck_6500_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_toProcess_6481_);
                        leanh::lean_inc(v_exprFVarArgs_6480_);
                        leanh::lean_inc(v_exprMVarArgs_6479_);
                        leanh::lean_inc(v_nextExprIdx_6478_);
                        leanh::lean_inc(v_newLetDecls_6477_);
                        leanh::lean_inc(v_newLocalDeclsForMVars_6476_);
                        leanh::lean_inc(v_newLocalDecls_6475_);
                        leanh::lean_inc(v_levelArgs_6474_);
                        leanh::lean_inc(v_nextLevelIdx_6473_);
                        leanh::lean_inc(v_levelParams_6472_);
                        leanh::lean_inc(v_visitedExpr_6471_);
                        leanh::lean_inc(v_visitedLevel_6470_);
                        leanh::lean_dec(v___x_6468_);
                        v___x_6483_ = leanh::lean_box(0);
                        v_isShared_6484_ = v_isSharedCheck_6500_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_6501_ = leanh::lean_box(0);
                    v___x_6502_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6502_, 0, v___x_6501_);
                    return v___x_6502_;
                }
            }
            1 => {
                v___x_6485_ = l_Lean_Meta_Closure_instInhabitedToProcessElement_default;
                v___x_6486_ = lean_array_get_size(v_toProcess_6481_);
                v___x_6487_ = leanh::lean_unsigned_to_nat(1);
                v___x_6488_ = lean_nat_sub(v___x_6486_, v___x_6487_);
                v___x_6489_ = lean_array_get(v___x_6485_, v_toProcess_6481_, v___x_6488_);
                leanh::lean_dec(v___x_6488_);
                v___x_6490_ = lean_array_pop(v_toProcess_6481_);
                leanh::lean_inc_ref(v_lctx_6469_);
                v___x_6491_ = l_Lean_Meta_Closure_pickNextToProcessAux(
                    v_lctx_6469_,
                    v___x_6466_,
                    v___x_6490_,
                    v___x_6489_,
                );
                v_fst_6492_ = leanh::lean_ctor_get(v___x_6491_, 0);
                leanh::lean_inc(v_fst_6492_);
                v_snd_6493_ = leanh::lean_ctor_get(v___x_6491_, 1);
                leanh::lean_inc(v_snd_6493_);
                leanh::lean_dec_ref(v___x_6491_);
                if v_isShared_6484_ == 0 {
                    leanh::lean_ctor_set(v___x_6483_, 11, v_snd_6493_);
                    v___x_6495_ = v___x_6483_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6499_ = leanh::lean_alloc_ctor(0, 12, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6499_, 0, v_visitedLevel_6470_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6499_, 1, v_visitedExpr_6471_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6499_, 2, v_levelParams_6472_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6499_, 3, v_nextLevelIdx_6473_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6499_, 4, v_levelArgs_6474_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6499_, 5, v_newLocalDecls_6475_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_6499_,
                        6,
                        v_newLocalDeclsForMVars_6476_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_6499_, 7, v_newLetDecls_6477_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6499_, 8, v_nextExprIdx_6478_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6499_, 9, v_exprMVarArgs_6479_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6499_, 10, v_exprFVarArgs_6480_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6499_, 11, v_snd_6493_);
                    v___x_6495_ = v_reuseFailAlloc_6499_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6496_ = lean_st_ref_set(v_a_6460_, v___x_6495_);
                v___x_6497_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6497_, 0, v_fst_6492_);
                v___x_6498_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6498_, 0, v___x_6497_);
                return v___x_6498_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg___boxed(
    mut v_a_6503_: *mut leanh::LeanObject,
    mut v_a_6504_: *mut leanh::LeanObject,
    mut v_a_6505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6506_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_6503_, v_a_6504_);
    leanh::lean_dec_ref(v_a_6504_);
    leanh::lean_dec(v_a_6503_);
    return v_res_6506_;
}
pub unsafe fn l_Lean_Meta_Closure_pickNextToProcess_x3f(
    mut v_a_6507_: u8,
    mut v_a_6508_: *mut leanh::LeanObject,
    mut v_a_6509_: *mut leanh::LeanObject,
    mut v_a_6510_: *mut leanh::LeanObject,
    mut v_a_6511_: *mut leanh::LeanObject,
    mut v_a_6512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6514_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_6508_, v_a_6509_);
    return v___x_6514_;
}
pub unsafe fn l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(
    mut v_a_6515_: *mut leanh::LeanObject,
    mut v_a_6516_: *mut leanh::LeanObject,
    mut v_a_6517_: *mut leanh::LeanObject,
    mut v_a_6518_: *mut leanh::LeanObject,
    mut v_a_6519_: *mut leanh::LeanObject,
    mut v_a_6520_: *mut leanh::LeanObject,
    mut v_a_6521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_6522_: u8 = 0;
    let mut v_res_6523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_6522_ = (leanh::lean_unbox(v_a_6515_) as u8);
    v_res_6523_ = l_Lean_Meta_Closure_pickNextToProcess_x3f(
        v_a_boxed_6522_,
        v_a_6516_,
        v_a_6517_,
        v_a_6518_,
        v_a_6519_,
        v_a_6520_,
    );
    leanh::lean_dec(v_a_6520_);
    leanh::lean_dec_ref(v_a_6519_);
    leanh::lean_dec(v_a_6518_);
    leanh::lean_dec_ref(v_a_6517_);
    leanh::lean_dec(v_a_6516_);
    return v_res_6523_;
}
pub unsafe fn l_Lean_Meta_Closure_pushFVarArg___redArg(
    mut v_e_6524_: *mut leanh::LeanObject,
    mut v_a_6525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_6528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_6529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_6530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextLevelIdx_6531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelArgs_6532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDecls_6533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDeclsForMVars_6534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLetDecls_6535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextExprIdx_6536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprMVarArgs_6537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprFVarArgs_6538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toProcess_6539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6542_: u8 = 0;
    let mut v___x_6543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6550_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6527_ = lean_st_ref_take(v_a_6525_);
                v_visitedLevel_6528_ = leanh::lean_ctor_get(v___x_6527_, 0);
                v_visitedExpr_6529_ = leanh::lean_ctor_get(v___x_6527_, 1);
                v_levelParams_6530_ = leanh::lean_ctor_get(v___x_6527_, 2);
                v_nextLevelIdx_6531_ = leanh::lean_ctor_get(v___x_6527_, 3);
                v_levelArgs_6532_ = leanh::lean_ctor_get(v___x_6527_, 4);
                v_newLocalDecls_6533_ = leanh::lean_ctor_get(v___x_6527_, 5);
                v_newLocalDeclsForMVars_6534_ = leanh::lean_ctor_get(v___x_6527_, 6);
                v_newLetDecls_6535_ = leanh::lean_ctor_get(v___x_6527_, 7);
                v_nextExprIdx_6536_ = leanh::lean_ctor_get(v___x_6527_, 8);
                v_exprMVarArgs_6537_ = leanh::lean_ctor_get(v___x_6527_, 9);
                v_exprFVarArgs_6538_ = leanh::lean_ctor_get(v___x_6527_, 10);
                v_toProcess_6539_ = leanh::lean_ctor_get(v___x_6527_, 11);
                v_isSharedCheck_6550_ = (!leanh::lean_is_exclusive(v___x_6527_)) as u8;
                if v_isSharedCheck_6550_ == 0 {
                    v___x_6541_ = v___x_6527_;
                    v_isShared_6542_ = v_isSharedCheck_6550_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toProcess_6539_);
                    leanh::lean_inc(v_exprFVarArgs_6538_);
                    leanh::lean_inc(v_exprMVarArgs_6537_);
                    leanh::lean_inc(v_nextExprIdx_6536_);
                    leanh::lean_inc(v_newLetDecls_6535_);
                    leanh::lean_inc(v_newLocalDeclsForMVars_6534_);
                    leanh::lean_inc(v_newLocalDecls_6533_);
                    leanh::lean_inc(v_levelArgs_6532_);
                    leanh::lean_inc(v_nextLevelIdx_6531_);
                    leanh::lean_inc(v_levelParams_6530_);
                    leanh::lean_inc(v_visitedExpr_6529_);
                    leanh::lean_inc(v_visitedLevel_6528_);
                    leanh::lean_dec(v___x_6527_);
                    v___x_6541_ = leanh::lean_box(0);
                    v_isShared_6542_ = v_isSharedCheck_6550_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6543_ = lean_array_push(v_exprFVarArgs_6538_, v_e_6524_);
                if v_isShared_6542_ == 0 {
                    leanh::lean_ctor_set(v___x_6541_, 10, v___x_6543_);
                    v___x_6545_ = v___x_6541_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6549_ = leanh::lean_alloc_ctor(0, 12, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6549_, 0, v_visitedLevel_6528_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6549_, 1, v_visitedExpr_6529_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6549_, 2, v_levelParams_6530_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6549_, 3, v_nextLevelIdx_6531_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6549_, 4, v_levelArgs_6532_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6549_, 5, v_newLocalDecls_6533_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_6549_,
                        6,
                        v_newLocalDeclsForMVars_6534_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_6549_, 7, v_newLetDecls_6535_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6549_, 8, v_nextExprIdx_6536_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6549_, 9, v_exprMVarArgs_6537_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6549_, 10, v___x_6543_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6549_, 11, v_toProcess_6539_);
                    v___x_6545_ = v_reuseFailAlloc_6549_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6546_ = lean_st_ref_set(v_a_6525_, v___x_6545_);
                v___x_6547_ = leanh::lean_box(0);
                v___x_6548_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6548_, 0, v___x_6547_);
                return v___x_6548_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Closure_pushFVarArg___redArg___boxed(
    mut v_e_6551_: *mut leanh::LeanObject,
    mut v_a_6552_: *mut leanh::LeanObject,
    mut v_a_6553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6554_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v_e_6551_, v_a_6552_);
    leanh::lean_dec(v_a_6552_);
    return v_res_6554_;
}
pub unsafe fn l_Lean_Meta_Closure_pushFVarArg(
    mut v_e_6555_: *mut leanh::LeanObject,
    mut v_a_6556_: u8,
    mut v_a_6557_: *mut leanh::LeanObject,
    mut v_a_6558_: *mut leanh::LeanObject,
    mut v_a_6559_: *mut leanh::LeanObject,
    mut v_a_6560_: *mut leanh::LeanObject,
    mut v_a_6561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6563_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v_e_6555_, v_a_6557_);
    return v___x_6563_;
}
pub unsafe fn l_Lean_Meta_Closure_pushFVarArg___boxed(
    mut v_e_6564_: *mut leanh::LeanObject,
    mut v_a_6565_: *mut leanh::LeanObject,
    mut v_a_6566_: *mut leanh::LeanObject,
    mut v_a_6567_: *mut leanh::LeanObject,
    mut v_a_6568_: *mut leanh::LeanObject,
    mut v_a_6569_: *mut leanh::LeanObject,
    mut v_a_6570_: *mut leanh::LeanObject,
    mut v_a_6571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_6572_: u8 = 0;
    let mut v_res_6573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_6572_ = (leanh::lean_unbox(v_a_6565_) as u8);
    v_res_6573_ = l_Lean_Meta_Closure_pushFVarArg(
        v_e_6564_,
        v_a_boxed_6572_,
        v_a_6566_,
        v_a_6567_,
        v_a_6568_,
        v_a_6569_,
        v_a_6570_,
    );
    leanh::lean_dec(v_a_6570_);
    leanh::lean_dec_ref(v_a_6569_);
    leanh::lean_dec(v_a_6568_);
    leanh::lean_dec_ref(v_a_6567_);
    leanh::lean_dec(v_a_6566_);
    return v_res_6573_;
}
pub unsafe fn l_Lean_Meta_Closure_pushLocalDecl(
    mut v_newFVarId_6574_: *mut leanh::LeanObject,
    mut v_userName_6575_: *mut leanh::LeanObject,
    mut v_type_6576_: *mut leanh::LeanObject,
    mut v_bi_6577_: u8,
    mut v_a_6578_: u8,
    mut v_a_6579_: *mut leanh::LeanObject,
    mut v_a_6580_: *mut leanh::LeanObject,
    mut v_a_6581_: *mut leanh::LeanObject,
    mut v_a_6582_: *mut leanh::LeanObject,
    mut v_a_6583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6589_: u8 = 0;
    let mut v___x_6590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_6591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_6592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_6593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextLevelIdx_6594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelArgs_6595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDecls_6596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDeclsForMVars_6597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLetDecls_6598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextExprIdx_6599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprMVarArgs_6600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprFVarArgs_6601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toProcess_6602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6605_: u8 = 0;
    let mut v___x_6606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6607_: u8 = 0;
    let mut v___x_6608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6618_: u8 = 0;
    let mut v_isSharedCheck_6619_: u8 = 0;
    let mut v_a_6620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6623_: u8 = 0;
    let mut v___x_6625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6627_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6585_ = l_Lean_Meta_Closure_collectExpr(
                    v_type_6576_,
                    v_a_6578_,
                    v_a_6579_,
                    v_a_6580_,
                    v_a_6581_,
                    v_a_6582_,
                    v_a_6583_,
                );
                if leanh::lean_obj_tag(v___x_6585_) == 0 {
                    v_a_6586_ = leanh::lean_ctor_get(v___x_6585_, 0);
                    v_isSharedCheck_6619_ = (!leanh::lean_is_exclusive(v___x_6585_)) as u8;
                    if v_isSharedCheck_6619_ == 0 {
                        v___x_6588_ = v___x_6585_;
                        v_isShared_6589_ = v_isSharedCheck_6619_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6586_);
                        leanh::lean_dec(v___x_6585_);
                        v___x_6588_ = leanh::lean_box(0);
                        v_isShared_6589_ = v_isSharedCheck_6619_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_userName_6575_);
                    leanh::lean_dec(v_newFVarId_6574_);
                    v_a_6620_ = leanh::lean_ctor_get(v___x_6585_, 0);
                    v_isSharedCheck_6627_ = (!leanh::lean_is_exclusive(v___x_6585_)) as u8;
                    if v_isSharedCheck_6627_ == 0 {
                        v___x_6622_ = v___x_6585_;
                        v_isShared_6623_ = v_isSharedCheck_6627_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6620_);
                        leanh::lean_dec(v___x_6585_);
                        v___x_6622_ = leanh::lean_box(0);
                        v_isShared_6623_ = v_isSharedCheck_6627_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6590_ = lean_st_ref_take(v_a_6579_);
                v_visitedLevel_6591_ = leanh::lean_ctor_get(v___x_6590_, 0);
                v_visitedExpr_6592_ = leanh::lean_ctor_get(v___x_6590_, 1);
                v_levelParams_6593_ = leanh::lean_ctor_get(v___x_6590_, 2);
                v_nextLevelIdx_6594_ = leanh::lean_ctor_get(v___x_6590_, 3);
                v_levelArgs_6595_ = leanh::lean_ctor_get(v___x_6590_, 4);
                v_newLocalDecls_6596_ = leanh::lean_ctor_get(v___x_6590_, 5);
                v_newLocalDeclsForMVars_6597_ = leanh::lean_ctor_get(v___x_6590_, 6);
                v_newLetDecls_6598_ = leanh::lean_ctor_get(v___x_6590_, 7);
                v_nextExprIdx_6599_ = leanh::lean_ctor_get(v___x_6590_, 8);
                v_exprMVarArgs_6600_ = leanh::lean_ctor_get(v___x_6590_, 9);
                v_exprFVarArgs_6601_ = leanh::lean_ctor_get(v___x_6590_, 10);
                v_toProcess_6602_ = leanh::lean_ctor_get(v___x_6590_, 11);
                v_isSharedCheck_6618_ = (!leanh::lean_is_exclusive(v___x_6590_)) as u8;
                if v_isSharedCheck_6618_ == 0 {
                    v___x_6604_ = v___x_6590_;
                    v_isShared_6605_ = v_isSharedCheck_6618_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toProcess_6602_);
                    leanh::lean_inc(v_exprFVarArgs_6601_);
                    leanh::lean_inc(v_exprMVarArgs_6600_);
                    leanh::lean_inc(v_nextExprIdx_6599_);
                    leanh::lean_inc(v_newLetDecls_6598_);
                    leanh::lean_inc(v_newLocalDeclsForMVars_6597_);
                    leanh::lean_inc(v_newLocalDecls_6596_);
                    leanh::lean_inc(v_levelArgs_6595_);
                    leanh::lean_inc(v_nextLevelIdx_6594_);
                    leanh::lean_inc(v_levelParams_6593_);
                    leanh::lean_inc(v_visitedExpr_6592_);
                    leanh::lean_inc(v_visitedLevel_6591_);
                    leanh::lean_dec(v___x_6590_);
                    v___x_6604_ = leanh::lean_box(0);
                    v_isShared_6605_ = v_isSharedCheck_6618_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6606_ = leanh::lean_unsigned_to_nat(0);
                v___x_6607_ = 0;
                v___x_6608_ = leanh::lean_alloc_ctor(0, 4, (2) as u32);
                leanh::lean_ctor_set(v___x_6608_, 0, v___x_6606_);
                leanh::lean_ctor_set(v___x_6608_, 1, v_newFVarId_6574_);
                leanh::lean_ctor_set(v___x_6608_, 2, v_userName_6575_);
                leanh::lean_ctor_set(v___x_6608_, 3, v_a_6586_);
                leanh::lean_ctor_set_uint8(
                    v___x_6608_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v_bi_6577_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6608_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
                    v___x_6607_,
                );
                v___x_6609_ = lean_array_push(v_newLocalDecls_6596_, v___x_6608_);
                if v_isShared_6605_ == 0 {
                    leanh::lean_ctor_set(v___x_6604_, 5, v___x_6609_);
                    v___x_6611_ = v___x_6604_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6617_ = leanh::lean_alloc_ctor(0, 12, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6617_, 0, v_visitedLevel_6591_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6617_, 1, v_visitedExpr_6592_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6617_, 2, v_levelParams_6593_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6617_, 3, v_nextLevelIdx_6594_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6617_, 4, v_levelArgs_6595_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6617_, 5, v___x_6609_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_6617_,
                        6,
                        v_newLocalDeclsForMVars_6597_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_6617_, 7, v_newLetDecls_6598_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6617_, 8, v_nextExprIdx_6599_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6617_, 9, v_exprMVarArgs_6600_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6617_, 10, v_exprFVarArgs_6601_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6617_, 11, v_toProcess_6602_);
                    v___x_6611_ = v_reuseFailAlloc_6617_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6612_ = lean_st_ref_set(v_a_6579_, v___x_6611_);
                v___x_6613_ = leanh::lean_box(0);
                if v_isShared_6589_ == 0 {
                    leanh::lean_ctor_set(v___x_6588_, 0, v___x_6613_);
                    v___x_6615_ = v___x_6588_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6616_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6616_, 0, v___x_6613_);
                    v___x_6615_ = v_reuseFailAlloc_6616_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6615_;
            }
            5 => {
                if v_isShared_6623_ == 0 {
                    v___x_6625_ = v___x_6622_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6626_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6626_, 0, v_a_6620_);
                    v___x_6625_ = v_reuseFailAlloc_6626_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6625_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Closure_pushLocalDecl___boxed(
    mut v_newFVarId_6628_: *mut leanh::LeanObject,
    mut v_userName_6629_: *mut leanh::LeanObject,
    mut v_type_6630_: *mut leanh::LeanObject,
    mut v_bi_6631_: *mut leanh::LeanObject,
    mut v_a_6632_: *mut leanh::LeanObject,
    mut v_a_6633_: *mut leanh::LeanObject,
    mut v_a_6634_: *mut leanh::LeanObject,
    mut v_a_6635_: *mut leanh::LeanObject,
    mut v_a_6636_: *mut leanh::LeanObject,
    mut v_a_6637_: *mut leanh::LeanObject,
    mut v_a_6638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_6639_: u8 = 0;
    let mut v_a_boxed_6640_: u8 = 0;
    let mut v_res_6641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_6639_ = (leanh::lean_unbox(v_bi_6631_) as u8);
    v_a_boxed_6640_ = (leanh::lean_unbox(v_a_6632_) as u8);
    v_res_6641_ = l_Lean_Meta_Closure_pushLocalDecl(
        v_newFVarId_6628_,
        v_userName_6629_,
        v_type_6630_,
        v_bi_boxed_6639_,
        v_a_boxed_6640_,
        v_a_6633_,
        v_a_6634_,
        v_a_6635_,
        v_a_6636_,
        v_a_6637_,
    );
    leanh::lean_dec(v_a_6637_);
    leanh::lean_dec_ref(v_a_6636_);
    leanh::lean_dec(v_a_6635_);
    leanh::lean_dec_ref(v_a_6634_);
    leanh::lean_dec(v_a_6633_);
    return v_res_6641_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(
    mut v_k_6642_: *mut leanh::LeanObject,
    mut v_t_6643_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_k_6644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6647_: u8 = 0;
    let mut v___x_6649_: u8 = 0;
    let mut v___x_6651_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_6643_) == 0 {
                    v_k_6644_ = leanh::lean_ctor_get(v_t_6643_, 1);
                    v_l_6645_ = leanh::lean_ctor_get(v_t_6643_, 3);
                    v_r_6646_ = leanh::lean_ctor_get(v_t_6643_, 4);
                    v___x_6647_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_6642_, v_k_6644_);
                    match v___x_6647_ {
                        0 => {
                            v_t_6643_ = v_l_6645_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_6649_ = 1;
                            return v___x_6649_;
                        }
                        _ => {
                            v_t_6643_ = v_r_6646_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_6651_ = 0;
                    return v___x_6651_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg___boxed(
    mut v_k_6652_: *mut leanh::LeanObject,
    mut v_t_6653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6654_: u8 = 0;
    let mut v_r_6655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6654_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(
            v_k_6652_, v_t_6653_,
        );
    leanh::lean_dec(v_t_6653_);
    leanh::lean_dec(v_k_6652_);
    v_r_6655_ = leanh::lean_box((v_res_6654_) as usize);
    return v_r_6655_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(
    mut v_newFVarId_6656_: *mut leanh::LeanObject,
    mut v_a_6657_: *mut leanh::LeanObject,
    mut v_sz_6658_: usize,
    mut v_i_6659_: usize,
    mut v_bs_6660_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6661_: u8 = 0;
    let mut v_v_6662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6666_: usize = 0;
    let mut v___x_6667_: usize = 0;
    let mut v___x_6668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6661_ = lean_usize_dec_lt(v_i_6659_, v_sz_6658_);
                if v___x_6661_ == 0 {
                    leanh::lean_dec(v_newFVarId_6656_);
                    return v_bs_6660_;
                } else {
                    v_v_6662_ = lean_array_uget(v_bs_6660_, v_i_6659_);
                    v___x_6663_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_6664_ = lean_array_uset(v_bs_6660_, v_i_6659_, v___x_6663_);
                    leanh::lean_inc(v_newFVarId_6656_);
                    v___x_6665_ =
                        l_Lean_LocalDecl_replaceFVarId(v_newFVarId_6656_, v_a_6657_, v_v_6662_);
                    v___x_6666_ = 1usize;
                    v___x_6667_ = lean_usize_add(v_i_6659_, v___x_6666_);
                    v___x_6668_ = lean_array_uset(v_bs_x27_6664_, v_i_6659_, v___x_6665_);
                    v_i_6659_ = v___x_6667_;
                    v_bs_6660_ = v___x_6668_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1___boxed(
    mut v_newFVarId_6670_: *mut leanh::LeanObject,
    mut v_a_6671_: *mut leanh::LeanObject,
    mut v_sz_6672_: *mut leanh::LeanObject,
    mut v_i_6673_: *mut leanh::LeanObject,
    mut v_bs_6674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6675_: usize = 0;
    let mut v_i_boxed_6676_: usize = 0;
    let mut v_res_6677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6675_ = leanh::lean_unbox_usize(v_sz_6672_);
    leanh::lean_dec(v_sz_6672_);
    v_i_boxed_6676_ = leanh::lean_unbox_usize(v_i_6673_);
    leanh::lean_dec(v_i_6673_);
    v_res_6677_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(v_newFVarId_6670_, v_a_6671_, v_sz_boxed_6675_, v_i_boxed_6676_, v_bs_6674_);
    leanh::lean_dec_ref(v_a_6671_);
    return v_res_6677_;
}
pub unsafe fn l_Lean_Meta_Closure_process(
    mut v_a_6678_: u8,
    mut v_a_6679_: *mut leanh::LeanObject,
    mut v_a_6680_: *mut leanh::LeanObject,
    mut v_a_6681_: *mut leanh::LeanObject,
    mut v_a_6682_: *mut leanh::LeanObject,
    mut v_a_6683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6689_: u8 = 0;
    let mut v___x_6690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newFVarId_6696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_6699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bi_6701_: u8 = 0;
    let mut v___x_6702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_6706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_6709_: u8 = 0;
    let mut v___x_6711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6712_: u8 = 0;
    let mut v___x_6713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6716_: u8 = 0;
    let mut v___x_6717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6721_: u8 = 0;
    let mut v___x_6722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_6727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_6728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_6729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextLevelIdx_6730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelArgs_6731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDecls_6732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDeclsForMVars_6733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLetDecls_6734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextExprIdx_6735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprMVarArgs_6736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprFVarArgs_6737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toProcess_6738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6741_: u8 = 0;
    let mut v___x_6742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6743_: u8 = 0;
    let mut v___x_6745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_6751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_6752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_6753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextLevelIdx_6754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelArgs_6755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDecls_6756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDeclsForMVars_6757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLetDecls_6758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextExprIdx_6759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprMVarArgs_6760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprFVarArgs_6761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toProcess_6762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6765_: u8 = 0;
    let mut v_sz_6766_: usize = 0;
    let mut v___x_6767_: usize = 0;
    let mut v___x_6768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6774_: u8 = 0;
    let mut v_reuseFailAlloc_6775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6777_: u8 = 0;
    let mut v_a_6778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6781_: u8 = 0;
    let mut v___x_6783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6785_: u8 = 0;
    let mut v_a_6786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6789_: u8 = 0;
    let mut v___x_6791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6793_: u8 = 0;
    let mut v_a_6794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6797_: u8 = 0;
    let mut v___x_6799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6801_: u8 = 0;
    let mut v_isSharedCheck_6802_: u8 = 0;
    let mut v_unused_6803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6808_: u8 = 0;
    let mut v___x_6810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6812_: u8 = 0;
    let mut v_isSharedCheck_6813_: u8 = 0;
    let mut v_a_6814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6817_: u8 = 0;
    let mut v___x_6819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6821_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6685_ =
                    l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_6679_, v_a_6680_);
                if leanh::lean_obj_tag(v___x_6685_) == 0 {
                    v_a_6686_ = leanh::lean_ctor_get(v___x_6685_, 0);
                    v_isSharedCheck_6813_ = (!leanh::lean_is_exclusive(v___x_6685_)) as u8;
                    if v_isSharedCheck_6813_ == 0 {
                        v___x_6688_ = v___x_6685_;
                        v_isShared_6689_ = v_isSharedCheck_6813_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6686_);
                        leanh::lean_dec(v___x_6685_);
                        v___x_6688_ = leanh::lean_box(0);
                        v_isShared_6689_ = v_isSharedCheck_6813_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6814_ = leanh::lean_ctor_get(v___x_6685_, 0);
                    v_isSharedCheck_6821_ = (!leanh::lean_is_exclusive(v___x_6685_)) as u8;
                    if v_isSharedCheck_6821_ == 0 {
                        v___x_6816_ = v___x_6685_;
                        v_isShared_6817_ = v_isSharedCheck_6821_;
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6814_);
                        leanh::lean_dec(v___x_6685_);
                        v___x_6816_ = leanh::lean_box(0);
                        v_isShared_6817_ = v_isSharedCheck_6821_;
                        state = 18;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_6686_) == 0 {
                    v___x_6690_ = leanh::lean_box(0);
                    if v_isShared_6689_ == 0 {
                        leanh::lean_ctor_set(v___x_6688_, 0, v___x_6690_);
                        v___x_6692_ = v___x_6688_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6693_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6693_, 0, v___x_6690_);
                        v___x_6692_ = v_reuseFailAlloc_6693_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6688_);
                    v_val_6694_ = leanh::lean_ctor_get(v_a_6686_, 0);
                    leanh::lean_inc(v_val_6694_);
                    leanh::lean_dec_ref_known(v_a_6686_, 1);
                    v_fvarId_6695_ = leanh::lean_ctor_get(v_val_6694_, 0);
                    leanh::lean_inc_n(v_fvarId_6695_, 2);
                    v_newFVarId_6696_ = leanh::lean_ctor_get(v_val_6694_, 1);
                    leanh::lean_inc(v_newFVarId_6696_);
                    leanh::lean_dec(v_val_6694_);
                    v___x_6697_ = l_Lean_FVarId_getDecl___redArg(
                        v_fvarId_6695_,
                        v_a_6680_,
                        v_a_6682_,
                        v_a_6683_,
                    );
                    if leanh::lean_obj_tag(v___x_6697_) == 0 {
                        v_a_6698_ = leanh::lean_ctor_get(v___x_6697_, 0);
                        leanh::lean_inc(v_a_6698_);
                        leanh::lean_dec_ref_known(v___x_6697_, 1);
                        if leanh::lean_obj_tag(v_a_6698_) == 0 {
                            v_userName_6699_ = leanh::lean_ctor_get(v_a_6698_, 2);
                            leanh::lean_inc(v_userName_6699_);
                            v_type_6700_ = leanh::lean_ctor_get(v_a_6698_, 3);
                            leanh::lean_inc_ref(v_type_6700_);
                            v_bi_6701_ = leanh::lean_ctor_get_uint8(
                                v_a_6698_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                            );
                            leanh::lean_dec_ref_known(v_a_6698_, 4);
                            v___x_6702_ = l_Lean_Meta_Closure_pushLocalDecl(
                                v_newFVarId_6696_,
                                v_userName_6699_,
                                v_type_6700_,
                                v_bi_6701_,
                                v_a_6678_,
                                v_a_6679_,
                                v_a_6680_,
                                v_a_6681_,
                                v_a_6682_,
                                v_a_6683_,
                            );
                            if leanh::lean_obj_tag(v___x_6702_) == 0 {
                                leanh::lean_dec_ref_known(v___x_6702_, 1);
                                v___x_6703_ = l_Lean_mkFVar(v_fvarId_6695_);
                                v___x_6704_ = l_Lean_Meta_Closure_pushFVarArg___redArg(
                                    v___x_6703_,
                                    v_a_6679_,
                                );
                                if leanh::lean_obj_tag(v___x_6704_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_6704_, 1);
                                    state = 0;
                                    continue;
                                } else {
                                    return v___x_6704_;
                                }
                            } else {
                                leanh::lean_dec(v_fvarId_6695_);
                                return v___x_6702_;
                            }
                        } else {
                            v_userName_6706_ = leanh::lean_ctor_get(v_a_6698_, 2);
                            v_type_6707_ = leanh::lean_ctor_get(v_a_6698_, 3);
                            v_value_6708_ = leanh::lean_ctor_get(v_a_6698_, 4);
                            v_nondep_6709_ = leanh::lean_ctor_get_uint8(
                                v_a_6698_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                            );
                            v_isSharedCheck_6802_ =
                                (!leanh::lean_is_exclusive(v_a_6698_)) as u8;
                            if v_isSharedCheck_6802_ == 0 {
                                v_unused_6803_ = leanh::lean_ctor_get(v_a_6698_, 1);
                                leanh::lean_dec(v_unused_6803_);
                                v_unused_6804_ = leanh::lean_ctor_get(v_a_6698_, 0);
                                leanh::lean_dec(v_unused_6804_);
                                v___x_6711_ = v_a_6698_;
                                v_isShared_6712_ = v_isSharedCheck_6802_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_value_6708_);
                                leanh::lean_inc(v_type_6707_);
                                leanh::lean_inc(v_userName_6706_);
                                leanh::lean_dec(v_a_6698_);
                                v___x_6711_ = leanh::lean_box(0);
                                v_isShared_6712_ = v_isSharedCheck_6802_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_newFVarId_6696_);
                        leanh::lean_dec(v_fvarId_6695_);
                        v_a_6805_ = leanh::lean_ctor_get(v___x_6697_, 0);
                        v_isSharedCheck_6812_ =
                            (!leanh::lean_is_exclusive(v___x_6697_)) as u8;
                        if v_isSharedCheck_6812_ == 0 {
                            v___x_6807_ = v___x_6697_;
                            v_isShared_6808_ = v_isSharedCheck_6812_;
                            state = 16;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6805_);
                            leanh::lean_dec(v___x_6697_);
                            v___x_6807_ = leanh::lean_box(0);
                            v_isShared_6808_ = v_isSharedCheck_6812_;
                            state = 16;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_6692_;
            }
            3 => {
                v___x_6713_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v_a_6681_);
                if leanh::lean_obj_tag(v___x_6713_) == 0 {
                    v_a_6714_ = leanh::lean_ctor_get(v___x_6713_, 0);
                    leanh::lean_inc(v_a_6714_);
                    leanh::lean_dec_ref_known(v___x_6713_, 1);
                    if v_nondep_6709_ == 0 {
                        v___x_6721_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_fvarId_6695_, v_a_6714_);
                        leanh::lean_dec(v_a_6714_);
                        if v___x_6721_ == 0 {
                            leanh::lean_del_object(v___x_6711_);
                            leanh::lean_dec_ref(v_value_6708_);
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_dec(v_fvarId_6695_);
                            v___x_6722_ = l_Lean_Meta_Closure_collectExpr(
                                v_type_6707_,
                                v_a_6678_,
                                v_a_6679_,
                                v_a_6680_,
                                v_a_6681_,
                                v_a_6682_,
                                v_a_6683_,
                            );
                            if leanh::lean_obj_tag(v___x_6722_) == 0 {
                                v_a_6723_ = leanh::lean_ctor_get(v___x_6722_, 0);
                                leanh::lean_inc(v_a_6723_);
                                leanh::lean_dec_ref_known(v___x_6722_, 1);
                                v___x_6724_ = l_Lean_Meta_Closure_collectExpr(
                                    v_value_6708_,
                                    v_a_6678_,
                                    v_a_6679_,
                                    v_a_6680_,
                                    v_a_6681_,
                                    v_a_6682_,
                                    v_a_6683_,
                                );
                                if leanh::lean_obj_tag(v___x_6724_) == 0 {
                                    v_a_6725_ = leanh::lean_ctor_get(v___x_6724_, 0);
                                    leanh::lean_inc(v_a_6725_);
                                    leanh::lean_dec_ref_known(v___x_6724_, 1);
                                    v___x_6726_ = lean_st_ref_take(v_a_6679_);
                                    v_visitedLevel_6727_ =
                                        leanh::lean_ctor_get(v___x_6726_, 0);
                                    v_visitedExpr_6728_ =
                                        leanh::lean_ctor_get(v___x_6726_, 1);
                                    v_levelParams_6729_ =
                                        leanh::lean_ctor_get(v___x_6726_, 2);
                                    v_nextLevelIdx_6730_ =
                                        leanh::lean_ctor_get(v___x_6726_, 3);
                                    v_levelArgs_6731_ = leanh::lean_ctor_get(v___x_6726_, 4);
                                    v_newLocalDecls_6732_ =
                                        leanh::lean_ctor_get(v___x_6726_, 5);
                                    v_newLocalDeclsForMVars_6733_ =
                                        leanh::lean_ctor_get(v___x_6726_, 6);
                                    v_newLetDecls_6734_ =
                                        leanh::lean_ctor_get(v___x_6726_, 7);
                                    v_nextExprIdx_6735_ =
                                        leanh::lean_ctor_get(v___x_6726_, 8);
                                    v_exprMVarArgs_6736_ =
                                        leanh::lean_ctor_get(v___x_6726_, 9);
                                    v_exprFVarArgs_6737_ =
                                        leanh::lean_ctor_get(v___x_6726_, 10);
                                    v_toProcess_6738_ =
                                        leanh::lean_ctor_get(v___x_6726_, 11);
                                    v_isSharedCheck_6777_ =
                                        (!leanh::lean_is_exclusive(v___x_6726_)) as u8;
                                    if v_isSharedCheck_6777_ == 0 {
                                        v___x_6740_ = v___x_6726_;
                                        v_isShared_6741_ = v_isSharedCheck_6777_;
                                        state = 5;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_toProcess_6738_);
                                        leanh::lean_inc(v_exprFVarArgs_6737_);
                                        leanh::lean_inc(v_exprMVarArgs_6736_);
                                        leanh::lean_inc(v_nextExprIdx_6735_);
                                        leanh::lean_inc(v_newLetDecls_6734_);
                                        leanh::lean_inc(v_newLocalDeclsForMVars_6733_);
                                        leanh::lean_inc(v_newLocalDecls_6732_);
                                        leanh::lean_inc(v_levelArgs_6731_);
                                        leanh::lean_inc(v_nextLevelIdx_6730_);
                                        leanh::lean_inc(v_levelParams_6729_);
                                        leanh::lean_inc(v_visitedExpr_6728_);
                                        leanh::lean_inc(v_visitedLevel_6727_);
                                        leanh::lean_dec(v___x_6726_);
                                        v___x_6740_ = leanh::lean_box(0);
                                        v_isShared_6741_ = v_isSharedCheck_6777_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_6723_);
                                    leanh::lean_del_object(v___x_6711_);
                                    leanh::lean_dec(v_userName_6706_);
                                    leanh::lean_dec(v_newFVarId_6696_);
                                    v_a_6778_ = leanh::lean_ctor_get(v___x_6724_, 0);
                                    v_isSharedCheck_6785_ =
                                        (!leanh::lean_is_exclusive(v___x_6724_)) as u8;
                                    if v_isSharedCheck_6785_ == 0 {
                                        v___x_6780_ = v___x_6724_;
                                        v_isShared_6781_ = v_isSharedCheck_6785_;
                                        state = 10;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_6778_);
                                        leanh::lean_dec(v___x_6724_);
                                        v___x_6780_ = leanh::lean_box(0);
                                        v_isShared_6781_ = v_isSharedCheck_6785_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_del_object(v___x_6711_);
                                leanh::lean_dec_ref(v_value_6708_);
                                leanh::lean_dec(v_userName_6706_);
                                leanh::lean_dec(v_newFVarId_6696_);
                                v_a_6786_ = leanh::lean_ctor_get(v___x_6722_, 0);
                                v_isSharedCheck_6793_ =
                                    (!leanh::lean_is_exclusive(v___x_6722_)) as u8;
                                if v_isSharedCheck_6793_ == 0 {
                                    v___x_6788_ = v___x_6722_;
                                    v_isShared_6789_ = v_isSharedCheck_6793_;
                                    state = 12;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6786_);
                                    leanh::lean_dec(v___x_6722_);
                                    v___x_6788_ = leanh::lean_box(0);
                                    v_isShared_6789_ = v_isSharedCheck_6793_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_6714_);
                        leanh::lean_del_object(v___x_6711_);
                        leanh::lean_dec_ref(v_value_6708_);
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6711_);
                    leanh::lean_dec_ref(v_value_6708_);
                    leanh::lean_dec_ref(v_type_6707_);
                    leanh::lean_dec(v_userName_6706_);
                    leanh::lean_dec(v_newFVarId_6696_);
                    leanh::lean_dec(v_fvarId_6695_);
                    v_a_6794_ = leanh::lean_ctor_get(v___x_6713_, 0);
                    v_isSharedCheck_6801_ = (!leanh::lean_is_exclusive(v___x_6713_)) as u8;
                    if v_isSharedCheck_6801_ == 0 {
                        v___x_6796_ = v___x_6713_;
                        v_isShared_6797_ = v_isSharedCheck_6801_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6794_);
                        leanh::lean_dec(v___x_6713_);
                        v___x_6796_ = leanh::lean_box(0);
                        v_isShared_6797_ = v_isSharedCheck_6801_;
                        state = 14;
                        continue;
                    }
                }
            }
            4 => {
                v___x_6716_ = 0;
                v___x_6717_ = l_Lean_Meta_Closure_pushLocalDecl(
                    v_newFVarId_6696_,
                    v_userName_6706_,
                    v_type_6707_,
                    v___x_6716_,
                    v_a_6678_,
                    v_a_6679_,
                    v_a_6680_,
                    v_a_6681_,
                    v_a_6682_,
                    v_a_6683_,
                );
                if leanh::lean_obj_tag(v___x_6717_) == 0 {
                    leanh::lean_dec_ref_known(v___x_6717_, 1);
                    v___x_6718_ = l_Lean_mkFVar(v_fvarId_6695_);
                    v___x_6719_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v___x_6718_, v_a_6679_);
                    if leanh::lean_obj_tag(v___x_6719_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6719_, 1);
                        state = 0;
                        continue;
                    } else {
                        return v___x_6719_;
                    }
                } else {
                    leanh::lean_dec(v_fvarId_6695_);
                    return v___x_6717_;
                }
            }
            5 => {
                v___x_6742_ = leanh::lean_unsigned_to_nat(0);
                v___x_6743_ = 0;
                leanh::lean_inc(v_a_6725_);
                leanh::lean_inc(v_newFVarId_6696_);
                if v_isShared_6712_ == 0 {
                    leanh::lean_ctor_set(v___x_6711_, 4, v_a_6725_);
                    leanh::lean_ctor_set(v___x_6711_, 3, v_a_6723_);
                    leanh::lean_ctor_set(v___x_6711_, 1, v_newFVarId_6696_);
                    leanh::lean_ctor_set(v___x_6711_, 0, v___x_6742_);
                    v___x_6745_ = v___x_6711_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6776_ = leanh::lean_alloc_ctor(1, 5, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6776_, 0, v___x_6742_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6776_, 1, v_newFVarId_6696_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6776_, 2, v_userName_6706_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6776_, 3, v_a_6723_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6776_, 4, v_a_6725_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6776_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                        v_nondep_6709_,
                    );
                    v___x_6745_ = v_reuseFailAlloc_6776_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                leanh::lean_ctor_set_uint8(
                    v___x_6745_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___x_6743_,
                );
                v___x_6746_ = lean_array_push(v_newLetDecls_6734_, v___x_6745_);
                if v_isShared_6741_ == 0 {
                    leanh::lean_ctor_set(v___x_6740_, 7, v___x_6746_);
                    v___x_6748_ = v___x_6740_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6775_ = leanh::lean_alloc_ctor(0, 12, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6775_, 0, v_visitedLevel_6727_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6775_, 1, v_visitedExpr_6728_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6775_, 2, v_levelParams_6729_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6775_, 3, v_nextLevelIdx_6730_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6775_, 4, v_levelArgs_6731_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6775_, 5, v_newLocalDecls_6732_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_6775_,
                        6,
                        v_newLocalDeclsForMVars_6733_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_6775_, 7, v___x_6746_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6775_, 8, v_nextExprIdx_6735_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6775_, 9, v_exprMVarArgs_6736_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6775_, 10, v_exprFVarArgs_6737_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6775_, 11, v_toProcess_6738_);
                    v___x_6748_ = v_reuseFailAlloc_6775_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_6749_ = lean_st_ref_set(v_a_6679_, v___x_6748_);
                v___x_6750_ = lean_st_ref_take(v_a_6679_);
                v_visitedLevel_6751_ = leanh::lean_ctor_get(v___x_6750_, 0);
                v_visitedExpr_6752_ = leanh::lean_ctor_get(v___x_6750_, 1);
                v_levelParams_6753_ = leanh::lean_ctor_get(v___x_6750_, 2);
                v_nextLevelIdx_6754_ = leanh::lean_ctor_get(v___x_6750_, 3);
                v_levelArgs_6755_ = leanh::lean_ctor_get(v___x_6750_, 4);
                v_newLocalDecls_6756_ = leanh::lean_ctor_get(v___x_6750_, 5);
                v_newLocalDeclsForMVars_6757_ = leanh::lean_ctor_get(v___x_6750_, 6);
                v_newLetDecls_6758_ = leanh::lean_ctor_get(v___x_6750_, 7);
                v_nextExprIdx_6759_ = leanh::lean_ctor_get(v___x_6750_, 8);
                v_exprMVarArgs_6760_ = leanh::lean_ctor_get(v___x_6750_, 9);
                v_exprFVarArgs_6761_ = leanh::lean_ctor_get(v___x_6750_, 10);
                v_toProcess_6762_ = leanh::lean_ctor_get(v___x_6750_, 11);
                v_isSharedCheck_6774_ = (!leanh::lean_is_exclusive(v___x_6750_)) as u8;
                if v_isSharedCheck_6774_ == 0 {
                    v___x_6764_ = v___x_6750_;
                    v_isShared_6765_ = v_isSharedCheck_6774_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_toProcess_6762_);
                    leanh::lean_inc(v_exprFVarArgs_6761_);
                    leanh::lean_inc(v_exprMVarArgs_6760_);
                    leanh::lean_inc(v_nextExprIdx_6759_);
                    leanh::lean_inc(v_newLetDecls_6758_);
                    leanh::lean_inc(v_newLocalDeclsForMVars_6757_);
                    leanh::lean_inc(v_newLocalDecls_6756_);
                    leanh::lean_inc(v_levelArgs_6755_);
                    leanh::lean_inc(v_nextLevelIdx_6754_);
                    leanh::lean_inc(v_levelParams_6753_);
                    leanh::lean_inc(v_visitedExpr_6752_);
                    leanh::lean_inc(v_visitedLevel_6751_);
                    leanh::lean_dec(v___x_6750_);
                    v___x_6764_ = leanh::lean_box(0);
                    v_isShared_6765_ = v_isSharedCheck_6774_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_sz_6766_ = lean_array_size(v_newLocalDecls_6756_);
                v___x_6767_ = 0usize;
                v___x_6768_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(v_newFVarId_6696_, v_a_6725_, v_sz_6766_, v___x_6767_, v_newLocalDecls_6756_);
                leanh::lean_dec(v_a_6725_);
                if v_isShared_6765_ == 0 {
                    leanh::lean_ctor_set(v___x_6764_, 5, v___x_6768_);
                    v___x_6770_ = v___x_6764_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6773_ = leanh::lean_alloc_ctor(0, 12, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6773_, 0, v_visitedLevel_6751_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6773_, 1, v_visitedExpr_6752_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6773_, 2, v_levelParams_6753_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6773_, 3, v_nextLevelIdx_6754_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6773_, 4, v_levelArgs_6755_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6773_, 5, v___x_6768_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_6773_,
                        6,
                        v_newLocalDeclsForMVars_6757_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_6773_, 7, v_newLetDecls_6758_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6773_, 8, v_nextExprIdx_6759_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6773_, 9, v_exprMVarArgs_6760_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6773_, 10, v_exprFVarArgs_6761_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6773_, 11, v_toProcess_6762_);
                    v___x_6770_ = v_reuseFailAlloc_6773_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_6771_ = lean_st_ref_set(v_a_6679_, v___x_6770_);
                state = 0;
                continue;
            }
            10 => {
                if v_isShared_6781_ == 0 {
                    v___x_6783_ = v___x_6780_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6784_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6784_, 0, v_a_6778_);
                    v___x_6783_ = v_reuseFailAlloc_6784_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6783_;
            }
            12 => {
                if v_isShared_6789_ == 0 {
                    v___x_6791_ = v___x_6788_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6792_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6792_, 0, v_a_6786_);
                    v___x_6791_ = v_reuseFailAlloc_6792_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6791_;
            }
            14 => {
                if v_isShared_6797_ == 0 {
                    v___x_6799_ = v___x_6796_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6800_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6800_, 0, v_a_6794_);
                    v___x_6799_ = v_reuseFailAlloc_6800_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6799_;
            }
            16 => {
                if v_isShared_6808_ == 0 {
                    v___x_6810_ = v___x_6807_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6811_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6811_, 0, v_a_6805_);
                    v___x_6810_ = v_reuseFailAlloc_6811_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6810_;
            }
            18 => {
                if v_isShared_6817_ == 0 {
                    v___x_6819_ = v___x_6816_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_6820_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6820_, 0, v_a_6814_);
                    v___x_6819_ = v_reuseFailAlloc_6820_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_6819_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Closure_process___boxed(
    mut v_a_6822_: *mut leanh::LeanObject,
    mut v_a_6823_: *mut leanh::LeanObject,
    mut v_a_6824_: *mut leanh::LeanObject,
    mut v_a_6825_: *mut leanh::LeanObject,
    mut v_a_6826_: *mut leanh::LeanObject,
    mut v_a_6827_: *mut leanh::LeanObject,
    mut v_a_6828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_6829_: u8 = 0;
    let mut v_res_6830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_6829_ = (leanh::lean_unbox(v_a_6822_) as u8);
    v_res_6830_ = l_Lean_Meta_Closure_process(
        v_a_boxed_6829_,
        v_a_6823_,
        v_a_6824_,
        v_a_6825_,
        v_a_6826_,
        v_a_6827_,
    );
    leanh::lean_dec(v_a_6827_);
    leanh::lean_dec_ref(v_a_6826_);
    leanh::lean_dec(v_a_6825_);
    leanh::lean_dec_ref(v_a_6824_);
    leanh::lean_dec(v_a_6823_);
    return v_res_6830_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0(
    mut v_00_u03b2_6831_: *mut leanh::LeanObject,
    mut v_k_6832_: *mut leanh::LeanObject,
    mut v_t_6833_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6834_: u8 = 0;
    v___x_6834_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(
            v_k_6832_, v_t_6833_,
        );
    return v___x_6834_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___boxed(
    mut v_00_u03b2_6835_: *mut leanh::LeanObject,
    mut v_k_6836_: *mut leanh::LeanObject,
    mut v_t_6837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6838_: u8 = 0;
    let mut v_r_6839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6838_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0(
        v_00_u03b2_6835_,
        v_k_6836_,
        v_t_6837_,
    );
    leanh::lean_dec(v_t_6837_);
    leanh::lean_dec(v_k_6836_);
    v_r_6839_ = leanh::lean_box((v_res_6838_) as usize);
    return v_r_6839_;
}
pub unsafe fn l_Lean_Meta_Closure_mkBinding___lam__0(
    mut v_decls_6840_: *mut leanh::LeanObject,
    mut v_xs_6841_: *mut leanh::LeanObject,
    mut v_isLambda_6842_: u8,
    mut v_i_6843_: *mut leanh::LeanObject,
    mut v_x_6844_: *mut leanh::LeanObject,
    mut v_b_6845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_decl_6846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_decl_6846_ = lean_array_fget_borrowed(v_decls_6840_, v_i_6843_);
    if leanh::lean_obj_tag(v_decl_6846_) == 0 {
        let mut v_userName_6847_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_type_6848_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_bi_6849_: u8 = 0;
        let mut v_ty_6850_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_userName_6847_ = leanh::lean_ctor_get(v_decl_6846_, 2);
        v_type_6848_ = leanh::lean_ctor_get(v_decl_6846_, 3);
        v_bi_6849_ = leanh::lean_ctor_get_uint8(
            v_decl_6846_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
        );
        v_ty_6850_ = lean_expr_abstract_range(v_type_6848_, v_i_6843_, v_xs_6841_);
        if v_isLambda_6842_ == 0 {
            let mut v___x_6851_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_userName_6847_);
            v___x_6851_ = l_Lean_mkForall(v_userName_6847_, v_bi_6849_, v_ty_6850_, v_b_6845_);
            return v___x_6851_;
        } else {
            let mut v___x_6852_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_userName_6847_);
            v___x_6852_ = l_Lean_mkLambda(v_userName_6847_, v_bi_6849_, v_ty_6850_, v_b_6845_);
            return v___x_6852_;
        }
    } else {
        let mut v_userName_6853_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_type_6854_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_6855_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_nondep_6856_: u8 = 0;
        let mut v___x_6857_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6858_: u8 = 0;
        v_userName_6853_ = leanh::lean_ctor_get(v_decl_6846_, 2);
        v_type_6854_ = leanh::lean_ctor_get(v_decl_6846_, 3);
        v_value_6855_ = leanh::lean_ctor_get(v_decl_6846_, 4);
        v_nondep_6856_ = leanh::lean_ctor_get_uint8(
            v_decl_6846_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
        );
        v___x_6857_ = leanh::lean_unsigned_to_nat(0);
        v___x_6858_ = lean_expr_has_loose_bvar(v_b_6845_, v___x_6857_);
        if v___x_6858_ == 0 {
            let mut v___x_6859_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6860_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_6859_ = leanh::lean_unsigned_to_nat(1);
            v___x_6860_ = lean_expr_lower_loose_bvars(v_b_6845_, v___x_6859_, v___x_6859_);
            leanh::lean_dec_ref(v_b_6845_);
            return v___x_6860_;
        } else {
            let mut v_ty_6861_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_6862_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6863_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_ty_6861_ = lean_expr_abstract_range(v_type_6854_, v_i_6843_, v_xs_6841_);
            v_val_6862_ = lean_expr_abstract_range(v_value_6855_, v_i_6843_, v_xs_6841_);
            leanh::lean_inc(v_userName_6853_);
            v___x_6863_ = l_Lean_Expr_letE___override(
                v_userName_6853_,
                v_ty_6861_,
                v_val_6862_,
                v_b_6845_,
                v_nondep_6856_,
            );
            return v___x_6863_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Closure_mkBinding___lam__0___boxed(
    mut v_decls_6864_: *mut leanh::LeanObject,
    mut v_xs_6865_: *mut leanh::LeanObject,
    mut v_isLambda_6866_: *mut leanh::LeanObject,
    mut v_i_6867_: *mut leanh::LeanObject,
    mut v_x_6868_: *mut leanh::LeanObject,
    mut v_b_6869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isLambda_boxed_6870_: u8 = 0;
    let mut v_res_6871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isLambda_boxed_6870_ = (leanh::lean_unbox(v_isLambda_6866_) as u8);
    v_res_6871_ = l_Lean_Meta_Closure_mkBinding___lam__0(
        v_decls_6864_,
        v_xs_6865_,
        v_isLambda_boxed_6870_,
        v_i_6867_,
        v_x_6868_,
        v_b_6869_,
    );
    leanh::lean_dec(v_i_6867_);
    leanh::lean_dec_ref(v_xs_6865_);
    leanh::lean_dec_ref(v_decls_6864_);
    return v_res_6871_;
}
pub unsafe fn l_Lean_Meta_Closure_mkBinding(
    mut v_isLambda_6892_: u8,
    mut v_decls_6893_: *mut leanh::LeanObject,
    mut v_b_6894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6897_: usize = 0;
    let mut v___x_6898_: usize = 0;
    let mut v_xs_6899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_6902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6895_ = l_Lean_Meta_Closure_mkBinding___closed__0;
    v___x_6896_ = l_Lean_Meta_Closure_mkBinding___closed__10;
    v_sz_6897_ = lean_array_size(v_decls_6893_);
    v___x_6898_ = 0usize;
    leanh::lean_inc_ref_n(v_decls_6893_, 2);
    v_xs_6899_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6896_,
        v___f_6895_,
        v_sz_6897_,
        v___x_6898_,
        v_decls_6893_,
    );
    v___x_6900_ = leanh::lean_box((v_isLambda_6892_) as usize);
    leanh::lean_inc(v_xs_6899_);
    v___f_6901_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Closure_mkBinding___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_6901_, 0, v_decls_6893_);
    leanh::lean_closure_set(v___f_6901_, 1, v_xs_6899_);
    leanh::lean_closure_set(v___f_6901_, 2, v___x_6900_);
    v_b_6902_ = lean_expr_abstract(v_b_6894_, v_xs_6899_);
    leanh::lean_dec(v_xs_6899_);
    v___x_6903_ = lean_array_get_size(v_decls_6893_);
    leanh::lean_dec_ref(v_decls_6893_);
    v___x_6904_ = l_Nat_foldRev___redArg(v___x_6903_, v___f_6901_, v_b_6902_);
    return v___x_6904_;
}
pub unsafe fn l_Lean_Meta_Closure_mkBinding___boxed(
    mut v_isLambda_6905_: *mut leanh::LeanObject,
    mut v_decls_6906_: *mut leanh::LeanObject,
    mut v_b_6907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isLambda_boxed_6908_: u8 = 0;
    let mut v_res_6909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isLambda_boxed_6908_ = (leanh::lean_unbox(v_isLambda_6905_) as u8);
    v_res_6909_ = l_Lean_Meta_Closure_mkBinding(v_isLambda_boxed_6908_, v_decls_6906_, v_b_6907_);
    leanh::lean_dec_ref(v_b_6907_);
    return v_res_6909_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(
    mut v_sz_6910_: usize,
    mut v_i_6911_: usize,
    mut v_bs_6912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6913_: u8 = 0;
    let mut v_v_6914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6918_: usize = 0;
    let mut v___x_6919_: usize = 0;
    let mut v___x_6920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6913_ = lean_usize_dec_lt(v_i_6911_, v_sz_6910_);
                if v___x_6913_ == 0 {
                    return v_bs_6912_;
                } else {
                    v_v_6914_ = lean_array_uget(v_bs_6912_, v_i_6911_);
                    v___x_6915_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_6916_ = lean_array_uset(v_bs_6912_, v_i_6911_, v___x_6915_);
                    v___x_6917_ = l_Lean_LocalDecl_toExpr(v_v_6914_);
                    v___x_6918_ = 1usize;
                    v___x_6919_ = lean_usize_add(v_i_6911_, v___x_6918_);
                    v___x_6920_ = lean_array_uset(v_bs_x27_6916_, v_i_6911_, v___x_6917_);
                    v_i_6911_ = v___x_6919_;
                    v_bs_6912_ = v___x_6920_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0___boxed(
    mut v_sz_6922_: *mut leanh::LeanObject,
    mut v_i_6923_: *mut leanh::LeanObject,
    mut v_bs_6924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6925_: usize = 0;
    let mut v_i_boxed_6926_: usize = 0;
    let mut v_res_6927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6925_ = leanh::lean_unbox_usize(v_sz_6922_);
    leanh::lean_dec(v_sz_6922_);
    v_i_boxed_6926_ = leanh::lean_unbox_usize(v_i_6923_);
    leanh::lean_dec(v_i_6923_);
    v_res_6927_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_boxed_6925_, v_i_boxed_6926_, v_bs_6924_);
    return v_res_6927_;
}
pub unsafe fn l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(
    mut v_decls_6928_: *mut leanh::LeanObject,
    mut v_xs_6929_: *mut leanh::LeanObject,
    mut v_x_6930_: *mut leanh::LeanObject,
    mut v_x_6931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_6932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6933_: u8 = 0;
    let mut v_one_6934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_6935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_6936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_6937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bi_6939_: u8 = 0;
    let mut v_ty_6940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_6943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_6946_: u8 = 0;
    let mut v___x_6947_: u8 = 0;
    let mut v___x_6948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_6950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_6932_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_6933_ = lean_nat_dec_eq(v_x_6930_, v_zero_6932_);
                if v_isZero_6933_ == 1 {
                    leanh::lean_dec(v_x_6930_);
                    return v_x_6931_;
                } else {
                    v_one_6934_ = leanh::lean_unsigned_to_nat(1);
                    v_n_6935_ = lean_nat_sub(v_x_6930_, v_one_6934_);
                    leanh::lean_dec(v_x_6930_);
                    v_decl_6936_ = lean_array_fget_borrowed(v_decls_6928_, v_n_6935_);
                    if leanh::lean_obj_tag(v_decl_6936_) == 0 {
                        v_userName_6937_ = leanh::lean_ctor_get(v_decl_6936_, 2);
                        v_type_6938_ = leanh::lean_ctor_get(v_decl_6936_, 3);
                        v_bi_6939_ = leanh::lean_ctor_get_uint8(
                            v_decl_6936_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        );
                        v_ty_6940_ = lean_expr_abstract_range(v_type_6938_, v_n_6935_, v_xs_6929_);
                        leanh::lean_inc(v_userName_6937_);
                        v___x_6941_ =
                            l_Lean_mkLambda(v_userName_6937_, v_bi_6939_, v_ty_6940_, v_x_6931_);
                        v_x_6930_ = v_n_6935_;
                        v_x_6931_ = v___x_6941_;
                        state = 0;
                        continue;
                    } else {
                        v_userName_6943_ = leanh::lean_ctor_get(v_decl_6936_, 2);
                        v_type_6944_ = leanh::lean_ctor_get(v_decl_6936_, 3);
                        v_value_6945_ = leanh::lean_ctor_get(v_decl_6936_, 4);
                        v_nondep_6946_ = leanh::lean_ctor_get_uint8(
                            v_decl_6936_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                        );
                        v___x_6947_ = lean_expr_has_loose_bvar(v_x_6931_, v_zero_6932_);
                        if v___x_6947_ == 0 {
                            v___x_6948_ =
                                lean_expr_lower_loose_bvars(v_x_6931_, v_one_6934_, v_one_6934_);
                            leanh::lean_dec_ref(v_x_6931_);
                            v_x_6930_ = v_n_6935_;
                            v_x_6931_ = v___x_6948_;
                            state = 0;
                            continue;
                        } else {
                            v_ty_6950_ =
                                lean_expr_abstract_range(v_type_6944_, v_n_6935_, v_xs_6929_);
                            v_val_6951_ =
                                lean_expr_abstract_range(v_value_6945_, v_n_6935_, v_xs_6929_);
                            leanh::lean_inc(v_userName_6943_);
                            v___x_6952_ = l_Lean_Expr_letE___override(
                                v_userName_6943_,
                                v_ty_6950_,
                                v_val_6951_,
                                v_x_6931_,
                                v_nondep_6946_,
                            );
                            v_x_6930_ = v_n_6935_;
                            v_x_6931_ = v___x_6952_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1___boxed(
    mut v_decls_6954_: *mut leanh::LeanObject,
    mut v_xs_6955_: *mut leanh::LeanObject,
    mut v_x_6956_: *mut leanh::LeanObject,
    mut v_x_6957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6958_ =
        l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(
            v_decls_6954_,
            v_xs_6955_,
            v_x_6956_,
            v_x_6957_,
        );
    leanh::lean_dec_ref(v_xs_6955_);
    leanh::lean_dec_ref(v_decls_6954_);
    return v_res_6958_;
}
pub unsafe fn l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(
    mut v_decls_6959_: *mut leanh::LeanObject,
    mut v_xs_6960_: *mut leanh::LeanObject,
    mut v_x_6961_: *mut leanh::LeanObject,
    mut v_x_6962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_6963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6964_: u8 = 0;
    v_zero_6963_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_6964_ = lean_nat_dec_eq(v_x_6961_, v_zero_6963_);
    if v_isZero_6964_ == 1 {
        return v_x_6962_;
    } else {
        let mut v_one_6965_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_6966_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_decl_6967_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_one_6965_ = leanh::lean_unsigned_to_nat(1);
        v_n_6966_ = lean_nat_sub(v_x_6961_, v_one_6965_);
        v_decl_6967_ = lean_array_fget_borrowed(v_decls_6959_, v_n_6966_);
        if leanh::lean_obj_tag(v_decl_6967_) == 0 {
            let mut v_userName_6968_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_6969_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_bi_6970_: u8 = 0;
            let mut v_ty_6971_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6972_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6973_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_userName_6968_ = leanh::lean_ctor_get(v_decl_6967_, 2);
            v_type_6969_ = leanh::lean_ctor_get(v_decl_6967_, 3);
            v_bi_6970_ = leanh::lean_ctor_get_uint8(
                v_decl_6967_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
            );
            v_ty_6971_ = lean_expr_abstract_range(v_type_6969_, v_n_6966_, v_xs_6960_);
            leanh::lean_inc(v_userName_6968_);
            v___x_6972_ = l_Lean_mkLambda(v_userName_6968_, v_bi_6970_, v_ty_6971_, v_x_6962_);
            v___x_6973_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_6959_, v_xs_6960_, v_n_6966_, v___x_6972_);
            return v___x_6973_;
        } else {
            let mut v_userName_6974_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_6975_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_value_6976_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_nondep_6977_: u8 = 0;
            let mut v___x_6978_: u8 = 0;
            v_userName_6974_ = leanh::lean_ctor_get(v_decl_6967_, 2);
            v_type_6975_ = leanh::lean_ctor_get(v_decl_6967_, 3);
            v_value_6976_ = leanh::lean_ctor_get(v_decl_6967_, 4);
            v_nondep_6977_ = leanh::lean_ctor_get_uint8(
                v_decl_6967_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
            );
            v___x_6978_ = lean_expr_has_loose_bvar(v_x_6962_, v_zero_6963_);
            if v___x_6978_ == 0 {
                let mut v___x_6979_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6980_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_6979_ = lean_expr_lower_loose_bvars(v_x_6962_, v_one_6965_, v_one_6965_);
                leanh::lean_dec_ref(v_x_6962_);
                v___x_6980_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_6959_, v_xs_6960_, v_n_6966_, v___x_6979_);
                return v___x_6980_;
            } else {
                let mut v_ty_6981_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_val_6982_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6983_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6984_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_ty_6981_ = lean_expr_abstract_range(v_type_6975_, v_n_6966_, v_xs_6960_);
                v_val_6982_ = lean_expr_abstract_range(v_value_6976_, v_n_6966_, v_xs_6960_);
                leanh::lean_inc(v_userName_6974_);
                v___x_6983_ = l_Lean_Expr_letE___override(
                    v_userName_6974_,
                    v_ty_6981_,
                    v_val_6982_,
                    v_x_6962_,
                    v_nondep_6977_,
                );
                v___x_6984_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_6959_, v_xs_6960_, v_n_6966_, v___x_6983_);
                return v___x_6984_;
            }
        }
    }
}
pub unsafe fn l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1___boxed(
    mut v_decls_6985_: *mut leanh::LeanObject,
    mut v_xs_6986_: *mut leanh::LeanObject,
    mut v_x_6987_: *mut leanh::LeanObject,
    mut v_x_6988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6989_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(
        v_decls_6985_,
        v_xs_6986_,
        v_x_6987_,
        v_x_6988_,
    );
    leanh::lean_dec(v_x_6987_);
    leanh::lean_dec_ref(v_xs_6986_);
    leanh::lean_dec_ref(v_decls_6985_);
    return v_res_6989_;
}
pub unsafe fn l_Lean_Meta_Closure_mkLambda(
    mut v_decls_6990_: *mut leanh::LeanObject,
    mut v_b_6991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_6992_: usize = 0;
    let mut v___x_6993_: usize = 0;
    let mut v_xs_6994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_6995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_6992_ = lean_array_size(v_decls_6990_);
    v___x_6993_ = 0usize;
    leanh::lean_inc_ref(v_decls_6990_);
    v_xs_6994_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_6992_, v___x_6993_, v_decls_6990_);
    v_b_6995_ = lean_expr_abstract(v_b_6991_, v_xs_6994_);
    v___x_6996_ = lean_array_get_size(v_decls_6990_);
    v___x_6997_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(
        v_decls_6990_,
        v_xs_6994_,
        v___x_6996_,
        v_b_6995_,
    );
    leanh::lean_dec_ref(v_xs_6994_);
    leanh::lean_dec_ref(v_decls_6990_);
    return v___x_6997_;
}
pub unsafe fn l_Lean_Meta_Closure_mkLambda___boxed(
    mut v_decls_6998_: *mut leanh::LeanObject,
    mut v_b_6999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7000_ = l_Lean_Meta_Closure_mkLambda(v_decls_6998_, v_b_6999_);
    leanh::lean_dec_ref(v_b_6999_);
    return v_res_7000_;
}
pub unsafe fn l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(
    mut v_decls_7001_: *mut leanh::LeanObject,
    mut v_xs_7002_: *mut leanh::LeanObject,
    mut v_x_7003_: *mut leanh::LeanObject,
    mut v_x_7004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_7005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_7006_: u8 = 0;
    let mut v_one_7007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_7008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_7009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_7010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bi_7012_: u8 = 0;
    let mut v_ty_7013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_7016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_7019_: u8 = 0;
    let mut v___x_7020_: u8 = 0;
    let mut v___x_7021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_7023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_7005_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_7006_ = lean_nat_dec_eq(v_x_7003_, v_zero_7005_);
                if v_isZero_7006_ == 1 {
                    leanh::lean_dec(v_x_7003_);
                    return v_x_7004_;
                } else {
                    v_one_7007_ = leanh::lean_unsigned_to_nat(1);
                    v_n_7008_ = lean_nat_sub(v_x_7003_, v_one_7007_);
                    leanh::lean_dec(v_x_7003_);
                    v_decl_7009_ = lean_array_fget_borrowed(v_decls_7001_, v_n_7008_);
                    if leanh::lean_obj_tag(v_decl_7009_) == 0 {
                        v_userName_7010_ = leanh::lean_ctor_get(v_decl_7009_, 2);
                        v_type_7011_ = leanh::lean_ctor_get(v_decl_7009_, 3);
                        v_bi_7012_ = leanh::lean_ctor_get_uint8(
                            v_decl_7009_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        );
                        v_ty_7013_ = lean_expr_abstract_range(v_type_7011_, v_n_7008_, v_xs_7002_);
                        leanh::lean_inc(v_userName_7010_);
                        v___x_7014_ =
                            l_Lean_mkForall(v_userName_7010_, v_bi_7012_, v_ty_7013_, v_x_7004_);
                        v_x_7003_ = v_n_7008_;
                        v_x_7004_ = v___x_7014_;
                        state = 0;
                        continue;
                    } else {
                        v_userName_7016_ = leanh::lean_ctor_get(v_decl_7009_, 2);
                        v_type_7017_ = leanh::lean_ctor_get(v_decl_7009_, 3);
                        v_value_7018_ = leanh::lean_ctor_get(v_decl_7009_, 4);
                        v_nondep_7019_ = leanh::lean_ctor_get_uint8(
                            v_decl_7009_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                        );
                        v___x_7020_ = lean_expr_has_loose_bvar(v_x_7004_, v_zero_7005_);
                        if v___x_7020_ == 0 {
                            v___x_7021_ =
                                lean_expr_lower_loose_bvars(v_x_7004_, v_one_7007_, v_one_7007_);
                            leanh::lean_dec_ref(v_x_7004_);
                            v_x_7003_ = v_n_7008_;
                            v_x_7004_ = v___x_7021_;
                            state = 0;
                            continue;
                        } else {
                            v_ty_7023_ =
                                lean_expr_abstract_range(v_type_7017_, v_n_7008_, v_xs_7002_);
                            v_val_7024_ =
                                lean_expr_abstract_range(v_value_7018_, v_n_7008_, v_xs_7002_);
                            leanh::lean_inc(v_userName_7016_);
                            v___x_7025_ = l_Lean_Expr_letE___override(
                                v_userName_7016_,
                                v_ty_7023_,
                                v_val_7024_,
                                v_x_7004_,
                                v_nondep_7019_,
                            );
                            v_x_7003_ = v_n_7008_;
                            v_x_7004_ = v___x_7025_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0___boxed(
    mut v_decls_7027_: *mut leanh::LeanObject,
    mut v_xs_7028_: *mut leanh::LeanObject,
    mut v_x_7029_: *mut leanh::LeanObject,
    mut v_x_7030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7031_ =
        l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(
            v_decls_7027_,
            v_xs_7028_,
            v_x_7029_,
            v_x_7030_,
        );
    leanh::lean_dec_ref(v_xs_7028_);
    leanh::lean_dec_ref(v_decls_7027_);
    return v_res_7031_;
}
pub unsafe fn l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(
    mut v_decls_7032_: *mut leanh::LeanObject,
    mut v_xs_7033_: *mut leanh::LeanObject,
    mut v_x_7034_: *mut leanh::LeanObject,
    mut v_x_7035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_7036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_7037_: u8 = 0;
    v_zero_7036_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_7037_ = lean_nat_dec_eq(v_x_7034_, v_zero_7036_);
    if v_isZero_7037_ == 1 {
        return v_x_7035_;
    } else {
        let mut v_one_7038_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_7039_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_decl_7040_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_one_7038_ = leanh::lean_unsigned_to_nat(1);
        v_n_7039_ = lean_nat_sub(v_x_7034_, v_one_7038_);
        v_decl_7040_ = lean_array_fget_borrowed(v_decls_7032_, v_n_7039_);
        if leanh::lean_obj_tag(v_decl_7040_) == 0 {
            let mut v_userName_7041_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_7042_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_bi_7043_: u8 = 0;
            let mut v_ty_7044_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7045_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7046_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_userName_7041_ = leanh::lean_ctor_get(v_decl_7040_, 2);
            v_type_7042_ = leanh::lean_ctor_get(v_decl_7040_, 3);
            v_bi_7043_ = leanh::lean_ctor_get_uint8(
                v_decl_7040_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
            );
            v_ty_7044_ = lean_expr_abstract_range(v_type_7042_, v_n_7039_, v_xs_7033_);
            leanh::lean_inc(v_userName_7041_);
            v___x_7045_ = l_Lean_mkForall(v_userName_7041_, v_bi_7043_, v_ty_7044_, v_x_7035_);
            v___x_7046_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_7032_, v_xs_7033_, v_n_7039_, v___x_7045_);
            return v___x_7046_;
        } else {
            let mut v_userName_7047_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_7048_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_value_7049_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_nondep_7050_: u8 = 0;
            let mut v___x_7051_: u8 = 0;
            v_userName_7047_ = leanh::lean_ctor_get(v_decl_7040_, 2);
            v_type_7048_ = leanh::lean_ctor_get(v_decl_7040_, 3);
            v_value_7049_ = leanh::lean_ctor_get(v_decl_7040_, 4);
            v_nondep_7050_ = leanh::lean_ctor_get_uint8(
                v_decl_7040_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
            );
            v___x_7051_ = lean_expr_has_loose_bvar(v_x_7035_, v_zero_7036_);
            if v___x_7051_ == 0 {
                let mut v___x_7052_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_7053_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_7052_ = lean_expr_lower_loose_bvars(v_x_7035_, v_one_7038_, v_one_7038_);
                leanh::lean_dec_ref(v_x_7035_);
                v___x_7053_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_7032_, v_xs_7033_, v_n_7039_, v___x_7052_);
                return v___x_7053_;
            } else {
                let mut v_ty_7054_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_val_7055_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_7056_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_7057_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_ty_7054_ = lean_expr_abstract_range(v_type_7048_, v_n_7039_, v_xs_7033_);
                v_val_7055_ = lean_expr_abstract_range(v_value_7049_, v_n_7039_, v_xs_7033_);
                leanh::lean_inc(v_userName_7047_);
                v___x_7056_ = l_Lean_Expr_letE___override(
                    v_userName_7047_,
                    v_ty_7054_,
                    v_val_7055_,
                    v_x_7035_,
                    v_nondep_7050_,
                );
                v___x_7057_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_7032_, v_xs_7033_, v_n_7039_, v___x_7056_);
                return v___x_7057_;
            }
        }
    }
}
pub unsafe fn l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0___boxed(
    mut v_decls_7058_: *mut leanh::LeanObject,
    mut v_xs_7059_: *mut leanh::LeanObject,
    mut v_x_7060_: *mut leanh::LeanObject,
    mut v_x_7061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7062_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(
        v_decls_7058_,
        v_xs_7059_,
        v_x_7060_,
        v_x_7061_,
    );
    leanh::lean_dec(v_x_7060_);
    leanh::lean_dec_ref(v_xs_7059_);
    leanh::lean_dec_ref(v_decls_7058_);
    return v_res_7062_;
}
pub unsafe fn l_Lean_Meta_Closure_mkForall(
    mut v_decls_7063_: *mut leanh::LeanObject,
    mut v_b_7064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_7065_: usize = 0;
    let mut v___x_7066_: usize = 0;
    let mut v_xs_7067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_7068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_7065_ = lean_array_size(v_decls_7063_);
    v___x_7066_ = 0usize;
    leanh::lean_inc_ref(v_decls_7063_);
    v_xs_7067_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_7065_, v___x_7066_, v_decls_7063_);
    v_b_7068_ = lean_expr_abstract(v_b_7064_, v_xs_7067_);
    v___x_7069_ = lean_array_get_size(v_decls_7063_);
    v___x_7070_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(
        v_decls_7063_,
        v_xs_7067_,
        v___x_7069_,
        v_b_7068_,
    );
    leanh::lean_dec_ref(v_xs_7067_);
    leanh::lean_dec_ref(v_decls_7063_);
    return v___x_7070_;
}
pub unsafe fn l_Lean_Meta_Closure_mkForall___boxed(
    mut v_decls_7071_: *mut leanh::LeanObject,
    mut v_b_7072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7073_ = l_Lean_Meta_Closure_mkForall(v_decls_7071_, v_b_7072_);
    leanh::lean_dec_ref(v_b_7072_);
    return v_res_7073_;
}
pub unsafe fn l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(
    mut v_a_7074_: *mut leanh::LeanObject,
    mut v_zetaDeltaFVarIds_7075_: *mut leanh::LeanObject,
    mut v_a_x3f_7076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_7079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_7081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_7082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7085_: u8 = 0;
    let mut v___x_7087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7092_: u8 = 0;
    let mut v_unused_7093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7078_ = lean_st_ref_take(v_a_7074_);
                v_mctx_7079_ = leanh::lean_ctor_get(v___x_7078_, 0);
                v_cache_7080_ = leanh::lean_ctor_get(v___x_7078_, 1);
                v_postponed_7081_ = leanh::lean_ctor_get(v___x_7078_, 3);
                v_diag_7082_ = leanh::lean_ctor_get(v___x_7078_, 4);
                v_isSharedCheck_7092_ = (!leanh::lean_is_exclusive(v___x_7078_)) as u8;
                if v_isSharedCheck_7092_ == 0 {
                    v_unused_7093_ = leanh::lean_ctor_get(v___x_7078_, 2);
                    leanh::lean_dec(v_unused_7093_);
                    v___x_7084_ = v___x_7078_;
                    v_isShared_7085_ = v_isSharedCheck_7092_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_7082_);
                    leanh::lean_inc(v_postponed_7081_);
                    leanh::lean_inc(v_cache_7080_);
                    leanh::lean_inc(v_mctx_7079_);
                    leanh::lean_dec(v___x_7078_);
                    v___x_7084_ = leanh::lean_box(0);
                    v_isShared_7085_ = v_isSharedCheck_7092_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_7085_ == 0 {
                    leanh::lean_ctor_set(v___x_7084_, 2, v_zetaDeltaFVarIds_7075_);
                    v___x_7087_ = v___x_7084_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7091_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7091_, 0, v_mctx_7079_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7091_, 1, v_cache_7080_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_7091_,
                        2,
                        v_zetaDeltaFVarIds_7075_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_7091_, 3, v_postponed_7081_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7091_, 4, v_diag_7082_);
                    v___x_7087_ = v_reuseFailAlloc_7091_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7088_ = lean_st_ref_set(v_a_7074_, v___x_7087_);
                v___x_7089_ = leanh::lean_box(0);
                v___x_7090_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7090_, 0, v___x_7089_);
                return v___x_7090_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0___boxed(
    mut v_a_7094_: *mut leanh::LeanObject,
    mut v_zetaDeltaFVarIds_7095_: *mut leanh::LeanObject,
    mut v_a_x3f_7096_: *mut leanh::LeanObject,
    mut v___y_7097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7098_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(
        v_a_7094_,
        v_zetaDeltaFVarIds_7095_,
        v_a_x3f_7096_,
    );
    leanh::lean_dec(v_a_x3f_7096_);
    leanh::lean_dec(v_a_7094_);
    return v_res_7098_;
}
pub unsafe fn l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(
    mut v_a_7099_: *mut leanh::LeanObject,
    mut v_cache_7100_: *mut leanh::LeanObject,
    mut v_a_x3f_7101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_7104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_7105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_7106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_7107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7110_: u8 = 0;
    let mut v___x_7112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7117_: u8 = 0;
    let mut v_unused_7118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7103_ = lean_st_ref_take(v_a_7099_);
                v_mctx_7104_ = leanh::lean_ctor_get(v___x_7103_, 0);
                v_zetaDeltaFVarIds_7105_ = leanh::lean_ctor_get(v___x_7103_, 2);
                v_postponed_7106_ = leanh::lean_ctor_get(v___x_7103_, 3);
                v_diag_7107_ = leanh::lean_ctor_get(v___x_7103_, 4);
                v_isSharedCheck_7117_ = (!leanh::lean_is_exclusive(v___x_7103_)) as u8;
                if v_isSharedCheck_7117_ == 0 {
                    v_unused_7118_ = leanh::lean_ctor_get(v___x_7103_, 1);
                    leanh::lean_dec(v_unused_7118_);
                    v___x_7109_ = v___x_7103_;
                    v_isShared_7110_ = v_isSharedCheck_7117_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_7107_);
                    leanh::lean_inc(v_postponed_7106_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_7105_);
                    leanh::lean_inc(v_mctx_7104_);
                    leanh::lean_dec(v___x_7103_);
                    v___x_7109_ = leanh::lean_box(0);
                    v_isShared_7110_ = v_isSharedCheck_7117_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_7110_ == 0 {
                    leanh::lean_ctor_set(v___x_7109_, 1, v_cache_7100_);
                    v___x_7112_ = v___x_7109_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7116_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7116_, 0, v_mctx_7104_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7116_, 1, v_cache_7100_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_7116_,
                        2,
                        v_zetaDeltaFVarIds_7105_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_7116_, 3, v_postponed_7106_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7116_, 4, v_diag_7107_);
                    v___x_7112_ = v_reuseFailAlloc_7116_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7113_ = lean_st_ref_set(v_a_7099_, v___x_7112_);
                v___x_7114_ = leanh::lean_box(0);
                v___x_7115_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7115_, 0, v___x_7114_);
                return v___x_7115_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1___boxed(
    mut v_a_7119_: *mut leanh::LeanObject,
    mut v_cache_7120_: *mut leanh::LeanObject,
    mut v_a_x3f_7121_: *mut leanh::LeanObject,
    mut v___y_7122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7123_ =
        l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_7119_, v_cache_7120_, v_a_x3f_7121_);
    leanh::lean_dec(v_a_x3f_7121_);
    leanh::lean_dec(v_a_7119_);
    return v_res_7123_;
}
pub unsafe fn _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_7124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7124_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_7124_;
}
pub unsafe fn _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_7125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7125_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0_once),
        _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0,
    );
    v___x_7126_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_7126_, 0, v___x_7125_);
    return v___x_7126_;
}
pub unsafe fn _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_7127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7127_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1_once),
        _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1,
    );
    v___x_7128_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_7128_, 0, v___x_7127_);
    leanh::lean_ctor_set(v___x_7128_, 1, v___x_7127_);
    leanh::lean_ctor_set(v___x_7128_, 2, v___x_7127_);
    leanh::lean_ctor_set(v___x_7128_, 3, v___x_7127_);
    leanh::lean_ctor_set(v___x_7128_, 4, v___x_7127_);
    leanh::lean_ctor_set(v___x_7128_, 5, v___x_7127_);
    return v___x_7128_;
}
pub unsafe fn l_Lean_Meta_Closure_mkValueTypeClosureAux(
    mut v_type_7129_: *mut leanh::LeanObject,
    mut v_value_7130_: *mut leanh::LeanObject,
    mut v_a_7131_: u8,
    mut v_a_7132_: *mut leanh::LeanObject,
    mut v_a_7133_: *mut leanh::LeanObject,
    mut v_a_7134_: *mut leanh::LeanObject,
    mut v_a_7135_: *mut leanh::LeanObject,
    mut v_a_7136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_7140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_7141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_7142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_7143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7146_: u8 = 0;
    let mut v___x_7147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_7152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_7154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_7155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_7156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7159_: u8 = 0;
    let mut v___x_7160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyedConfig_7165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaSet_7166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_7167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_7168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_7169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_7170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_7171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_7172_: u8 = 0;
    let mut v_inTypeClassResolution_7173_: u8 = 0;
    let mut v_cacheInferType_7174_: u8 = 0;
    let mut v_a_7176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7181_: u8 = 0;
    let mut v___x_7183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7185_: u8 = 0;
    let mut v_unused_7186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7191_: u8 = 0;
    let mut v___x_7192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7200_: u8 = 0;
    let mut v___x_7201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7208_: u8 = 0;
    let mut v___x_7210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7212_: u8 = 0;
    let mut v_unused_7213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7215_: u8 = 0;
    let mut v_unused_7216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7221_: u8 = 0;
    let mut v_reuseFailAlloc_7222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7223_: u8 = 0;
    let mut v_unused_7224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7138_ = lean_st_ref_get(v_a_7134_);
                v___x_7139_ = lean_st_ref_take(v_a_7134_);
                v_mctx_7140_ = leanh::lean_ctor_get(v___x_7139_, 0);
                v_zetaDeltaFVarIds_7141_ = leanh::lean_ctor_get(v___x_7139_, 2);
                v_postponed_7142_ = leanh::lean_ctor_get(v___x_7139_, 3);
                v_diag_7143_ = leanh::lean_ctor_get(v___x_7139_, 4);
                v_isSharedCheck_7223_ = (!leanh::lean_is_exclusive(v___x_7139_)) as u8;
                if v_isSharedCheck_7223_ == 0 {
                    v_unused_7224_ = leanh::lean_ctor_get(v___x_7139_, 1);
                    leanh::lean_dec(v_unused_7224_);
                    v___x_7145_ = v___x_7139_;
                    v_isShared_7146_ = v_isSharedCheck_7223_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_7143_);
                    leanh::lean_inc(v_postponed_7142_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_7141_);
                    leanh::lean_inc(v_mctx_7140_);
                    leanh::lean_dec(v___x_7139_);
                    v___x_7145_ = leanh::lean_box(0);
                    v_isShared_7146_ = v_isSharedCheck_7223_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7147_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2_once
                    ),
                    _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2,
                );
                if v_isShared_7146_ == 0 {
                    leanh::lean_ctor_set(v___x_7145_, 1, v___x_7147_);
                    v___x_7149_ = v___x_7145_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7222_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7222_, 0, v_mctx_7140_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7222_, 1, v___x_7147_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_7222_,
                        2,
                        v_zetaDeltaFVarIds_7141_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_7222_, 3, v_postponed_7142_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7222_, 4, v_diag_7143_);
                    v___x_7149_ = v_reuseFailAlloc_7222_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7150_ = lean_st_ref_set(v_a_7134_, v___x_7149_);
                v___x_7151_ = lean_st_ref_take(v_a_7134_);
                v_mctx_7152_ = leanh::lean_ctor_get(v___x_7151_, 0);
                v_cache_7153_ = leanh::lean_ctor_get(v___x_7151_, 1);
                v_zetaDeltaFVarIds_7154_ = leanh::lean_ctor_get(v___x_7151_, 2);
                v_postponed_7155_ = leanh::lean_ctor_get(v___x_7151_, 3);
                v_diag_7156_ = leanh::lean_ctor_get(v___x_7151_, 4);
                v_isSharedCheck_7221_ = (!leanh::lean_is_exclusive(v___x_7151_)) as u8;
                if v_isSharedCheck_7221_ == 0 {
                    v___x_7158_ = v___x_7151_;
                    v_isShared_7159_ = v_isSharedCheck_7221_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_7156_);
                    leanh::lean_inc(v_postponed_7155_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_7154_);
                    leanh::lean_inc(v_cache_7153_);
                    leanh::lean_inc(v_mctx_7152_);
                    leanh::lean_dec(v___x_7151_);
                    v___x_7158_ = leanh::lean_box(0);
                    v_isShared_7159_ = v_isSharedCheck_7221_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7160_ = leanh::lean_box(1);
                if v_isShared_7159_ == 0 {
                    leanh::lean_ctor_set(v___x_7158_, 2, v___x_7160_);
                    v___x_7162_ = v___x_7158_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7220_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7220_, 0, v_mctx_7152_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7220_, 1, v_cache_7153_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7220_, 2, v___x_7160_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7220_, 3, v_postponed_7155_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7220_, 4, v_diag_7156_);
                    v___x_7162_ = v_reuseFailAlloc_7220_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7163_ = lean_st_ref_set(v_a_7134_, v___x_7162_);
                v_cache_7164_ = leanh::lean_ctor_get(v___x_7138_, 1);
                leanh::lean_inc_ref(v_cache_7164_);
                leanh::lean_dec(v___x_7138_);
                v_keyedConfig_7165_ = leanh::lean_ctor_get(v_a_7133_, 0);
                v_zetaDeltaSet_7166_ = leanh::lean_ctor_get(v_a_7133_, 1);
                v_lctx_7167_ = leanh::lean_ctor_get(v_a_7133_, 2);
                v_localInstances_7168_ = leanh::lean_ctor_get(v_a_7133_, 3);
                v_defEqCtx_x3f_7169_ = leanh::lean_ctor_get(v_a_7133_, 4);
                v_synthPendingDepth_7170_ = leanh::lean_ctor_get(v_a_7133_, 5);
                v_canUnfold_x3f_7171_ = leanh::lean_ctor_get(v_a_7133_, 6);
                v_univApprox_7172_ = leanh::lean_ctor_get_uint8(
                    v_a_7133_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_7173_ = leanh::lean_ctor_get_uint8(
                    v_a_7133_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_7174_ = leanh::lean_ctor_get_uint8(
                    v_a_7133_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_7191_ = 1;
                leanh::lean_inc(v_canUnfold_x3f_7171_);
                leanh::lean_inc(v_synthPendingDepth_7170_);
                leanh::lean_inc(v_defEqCtx_x3f_7169_);
                leanh::lean_inc_ref(v_localInstances_7168_);
                leanh::lean_inc_ref(v_lctx_7167_);
                leanh::lean_inc(v_zetaDeltaSet_7166_);
                leanh::lean_inc_ref(v_keyedConfig_7165_);
                v___x_7192_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_7192_, 0, v_keyedConfig_7165_);
                leanh::lean_ctor_set(v___x_7192_, 1, v_zetaDeltaSet_7166_);
                leanh::lean_ctor_set(v___x_7192_, 2, v_lctx_7167_);
                leanh::lean_ctor_set(v___x_7192_, 3, v_localInstances_7168_);
                leanh::lean_ctor_set(v___x_7192_, 4, v_defEqCtx_x3f_7169_);
                leanh::lean_ctor_set(v___x_7192_, 5, v_synthPendingDepth_7170_);
                leanh::lean_ctor_set(v___x_7192_, 6, v_canUnfold_x3f_7171_);
                leanh::lean_ctor_set_uint8(
                    v___x_7192_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v___x_7191_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_7192_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_7172_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_7192_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_7173_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_7192_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_7174_,
                );
                v___x_7193_ = l_Lean_Meta_Closure_collectExpr(
                    v_type_7129_,
                    v_a_7131_,
                    v_a_7132_,
                    v___x_7192_,
                    v_a_7134_,
                    v_a_7135_,
                    v_a_7136_,
                );
                if leanh::lean_obj_tag(v___x_7193_) == 0 {
                    v_a_7194_ = leanh::lean_ctor_get(v___x_7193_, 0);
                    leanh::lean_inc(v_a_7194_);
                    leanh::lean_dec_ref_known(v___x_7193_, 1);
                    v___x_7195_ = l_Lean_Meta_Closure_collectExpr(
                        v_value_7130_,
                        v_a_7131_,
                        v_a_7132_,
                        v___x_7192_,
                        v_a_7134_,
                        v_a_7135_,
                        v_a_7136_,
                    );
                    if leanh::lean_obj_tag(v___x_7195_) == 0 {
                        v_a_7196_ = leanh::lean_ctor_get(v___x_7195_, 0);
                        leanh::lean_inc(v_a_7196_);
                        leanh::lean_dec_ref_known(v___x_7195_, 1);
                        v___x_7197_ = l_Lean_Meta_Closure_process(
                            v_a_7131_,
                            v_a_7132_,
                            v___x_7192_,
                            v_a_7134_,
                            v_a_7135_,
                            v_a_7136_,
                        );
                        leanh::lean_dec_ref_known(v___x_7192_, 7);
                        if leanh::lean_obj_tag(v___x_7197_) == 0 {
                            v_isSharedCheck_7215_ =
                                (!leanh::lean_is_exclusive(v___x_7197_)) as u8;
                            if v_isSharedCheck_7215_ == 0 {
                                v_unused_7216_ = leanh::lean_ctor_get(v___x_7197_, 0);
                                leanh::lean_dec(v_unused_7216_);
                                v___x_7199_ = v___x_7197_;
                                v_isShared_7200_ = v_isSharedCheck_7215_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_7197_);
                                v___x_7199_ = leanh::lean_box(0);
                                v_isShared_7200_ = v_isSharedCheck_7215_;
                                state = 9;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_7196_);
                            leanh::lean_dec(v_a_7194_);
                            v_a_7217_ = leanh::lean_ctor_get(v___x_7197_, 0);
                            leanh::lean_inc(v_a_7217_);
                            leanh::lean_dec_ref_known(v___x_7197_, 1);
                            v_a_7188_ = v_a_7217_;
                            state = 8;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_7194_);
                        leanh::lean_dec_ref_known(v___x_7192_, 7);
                        v_a_7218_ = leanh::lean_ctor_get(v___x_7195_, 0);
                        leanh::lean_inc(v_a_7218_);
                        leanh::lean_dec_ref_known(v___x_7195_, 1);
                        v_a_7188_ = v_a_7218_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_7192_, 7);
                    leanh::lean_dec_ref(v_value_7130_);
                    v_a_7219_ = leanh::lean_ctor_get(v___x_7193_, 0);
                    leanh::lean_inc(v_a_7219_);
                    leanh::lean_dec_ref_known(v___x_7193_, 1);
                    v_a_7188_ = v_a_7219_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_7177_ = leanh::lean_box(0);
                v___x_7178_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(
                    v_a_7134_,
                    v_cache_7164_,
                    v___x_7177_,
                );
                v_isSharedCheck_7185_ = (!leanh::lean_is_exclusive(v___x_7178_)) as u8;
                if v_isSharedCheck_7185_ == 0 {
                    v_unused_7186_ = leanh::lean_ctor_get(v___x_7178_, 0);
                    leanh::lean_dec(v_unused_7186_);
                    v___x_7180_ = v___x_7178_;
                    v_isShared_7181_ = v_isSharedCheck_7185_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec(v___x_7178_);
                    v___x_7180_ = leanh::lean_box(0);
                    v_isShared_7181_ = v_isSharedCheck_7185_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_7181_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_7180_, 1);
                    leanh::lean_ctor_set(v___x_7180_, 0, v_a_7176_);
                    v___x_7183_ = v___x_7180_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7184_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7184_, 0, v_a_7176_);
                    v___x_7183_ = v_reuseFailAlloc_7184_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7183_;
            }
            8 => {
                v___x_7189_ = leanh::lean_box(0);
                v___x_7190_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(
                    v_a_7134_,
                    v_zetaDeltaFVarIds_7154_,
                    v___x_7189_,
                );
                leanh::lean_dec_ref(v___x_7190_);
                v_a_7176_ = v_a_7188_;
                state = 5;
                continue;
            }
            9 => {
                v___x_7201_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7201_, 0, v_a_7194_);
                leanh::lean_ctor_set(v___x_7201_, 1, v_a_7196_);
                leanh::lean_inc_ref(v___x_7201_);
                if v_isShared_7200_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_7199_, 1);
                    leanh::lean_ctor_set(v___x_7199_, 0, v___x_7201_);
                    v___x_7203_ = v___x_7199_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7214_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7214_, 0, v___x_7201_);
                    v___x_7203_ = v_reuseFailAlloc_7214_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_7204_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(
                    v_a_7134_,
                    v_zetaDeltaFVarIds_7154_,
                    v___x_7203_,
                );
                leanh::lean_dec_ref(v___x_7204_);
                v___x_7205_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(
                    v_a_7134_,
                    v_cache_7164_,
                    v___x_7203_,
                );
                leanh::lean_dec_ref(v___x_7203_);
                v_isSharedCheck_7212_ = (!leanh::lean_is_exclusive(v___x_7205_)) as u8;
                if v_isSharedCheck_7212_ == 0 {
                    v_unused_7213_ = leanh::lean_ctor_get(v___x_7205_, 0);
                    leanh::lean_dec(v_unused_7213_);
                    v___x_7207_ = v___x_7205_;
                    v_isShared_7208_ = v_isSharedCheck_7212_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_dec(v___x_7205_);
                    v___x_7207_ = leanh::lean_box(0);
                    v_isShared_7208_ = v_isSharedCheck_7212_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_7208_ == 0 {
                    leanh::lean_ctor_set(v___x_7207_, 0, v___x_7201_);
                    v___x_7210_ = v___x_7207_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_7211_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7211_, 0, v___x_7201_);
                    v___x_7210_ = v_reuseFailAlloc_7211_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_7210_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(
    mut v_type_7225_: *mut leanh::LeanObject,
    mut v_value_7226_: *mut leanh::LeanObject,
    mut v_a_7227_: *mut leanh::LeanObject,
    mut v_a_7228_: *mut leanh::LeanObject,
    mut v_a_7229_: *mut leanh::LeanObject,
    mut v_a_7230_: *mut leanh::LeanObject,
    mut v_a_7231_: *mut leanh::LeanObject,
    mut v_a_7232_: *mut leanh::LeanObject,
    mut v_a_7233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_7234_: u8 = 0;
    let mut v_res_7235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_7234_ = (leanh::lean_unbox(v_a_7227_) as u8);
    v_res_7235_ = l_Lean_Meta_Closure_mkValueTypeClosureAux(
        v_type_7225_,
        v_value_7226_,
        v_a_boxed_7234_,
        v_a_7228_,
        v_a_7229_,
        v_a_7230_,
        v_a_7231_,
        v_a_7232_,
    );
    leanh::lean_dec(v_a_7232_);
    leanh::lean_dec_ref(v_a_7231_);
    leanh::lean_dec(v_a_7230_);
    leanh::lean_dec_ref(v_a_7229_);
    leanh::lean_dec(v_a_7228_);
    return v_res_7235_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_7236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7236_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_7236_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(
    mut v_msg_7239_: *mut leanh::LeanObject,
    mut v___y_7240_: *mut leanh::LeanObject,
    mut v___y_7241_: *mut leanh::LeanObject,
    mut v___y_7242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_7246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7249_: u8 = 0;
    let mut v_toFunctor_7250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_7251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_7252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_7253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7256_: u8 = 0;
    let mut v___f_7257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_14557__overap_7281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7285_: u8 = 0;
    let mut v_unused_7286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7287_: u8 = 0;
    let mut v_unused_7288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7244_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0);
                v___x_7245_ = l_StateRefT_x27_instMonad___redArg(v___x_7244_);
                v_toApplicative_7246_ = leanh::lean_ctor_get(v___x_7245_, 0);
                v_isSharedCheck_7287_ = (!leanh::lean_is_exclusive(v___x_7245_)) as u8;
                if v_isSharedCheck_7287_ == 0 {
                    v_unused_7288_ = leanh::lean_ctor_get(v___x_7245_, 1);
                    leanh::lean_dec(v_unused_7288_);
                    v___x_7248_ = v___x_7245_;
                    v_isShared_7249_ = v_isSharedCheck_7287_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_7246_);
                    leanh::lean_dec(v___x_7245_);
                    v___x_7248_ = leanh::lean_box(0);
                    v_isShared_7249_ = v_isSharedCheck_7287_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_7250_ = leanh::lean_ctor_get(v_toApplicative_7246_, 0);
                v_toSeq_7251_ = leanh::lean_ctor_get(v_toApplicative_7246_, 2);
                v_toSeqLeft_7252_ = leanh::lean_ctor_get(v_toApplicative_7246_, 3);
                v_toSeqRight_7253_ = leanh::lean_ctor_get(v_toApplicative_7246_, 4);
                v_isSharedCheck_7285_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_7246_)) as u8;
                if v_isSharedCheck_7285_ == 0 {
                    v_unused_7286_ = leanh::lean_ctor_get(v_toApplicative_7246_, 1);
                    leanh::lean_dec(v_unused_7286_);
                    v___x_7255_ = v_toApplicative_7246_;
                    v_isShared_7256_ = v_isSharedCheck_7285_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_7253_);
                    leanh::lean_inc(v_toSeqLeft_7252_);
                    leanh::lean_inc(v_toSeq_7251_);
                    leanh::lean_inc(v_toFunctor_7250_);
                    leanh::lean_dec(v_toApplicative_7246_);
                    v___x_7255_ = leanh::lean_box(0);
                    v_isShared_7256_ = v_isSharedCheck_7285_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_7257_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__1;
                v___f_7258_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__2;
                leanh::lean_inc_ref(v_toFunctor_7250_);
                v___f_7259_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_7259_, 0, v_toFunctor_7250_);
                v___f_7260_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_7260_, 0, v_toFunctor_7250_);
                v___x_7261_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7261_, 0, v___f_7259_);
                leanh::lean_ctor_set(v___x_7261_, 1, v___f_7260_);
                v___f_7262_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_7262_, 0, v_toSeqRight_7253_);
                v___f_7263_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_7263_, 0, v_toSeqLeft_7252_);
                v___f_7264_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_7264_, 0, v_toSeq_7251_);
                if v_isShared_7256_ == 0 {
                    leanh::lean_ctor_set(v___x_7255_, 4, v___f_7262_);
                    leanh::lean_ctor_set(v___x_7255_, 3, v___f_7263_);
                    leanh::lean_ctor_set(v___x_7255_, 2, v___f_7264_);
                    leanh::lean_ctor_set(v___x_7255_, 1, v___f_7257_);
                    leanh::lean_ctor_set(v___x_7255_, 0, v___x_7261_);
                    v___x_7266_ = v___x_7255_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7284_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7284_, 0, v___x_7261_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7284_, 1, v___f_7257_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7284_, 2, v___f_7264_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7284_, 3, v___f_7263_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7284_, 4, v___f_7262_);
                    v___x_7266_ = v_reuseFailAlloc_7284_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_7249_ == 0 {
                    leanh::lean_ctor_set(v___x_7248_, 1, v___f_7258_);
                    leanh::lean_ctor_set(v___x_7248_, 0, v___x_7266_);
                    v___x_7268_ = v___x_7248_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7283_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7283_, 0, v___x_7266_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7283_, 1, v___f_7258_);
                    v___x_7268_ = v_reuseFailAlloc_7283_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_inc_ref_n(v___x_7268_, 6);
                v___f_7269_ = leanh::lean_alloc_closure(
                    l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_7269_, 0, v___x_7268_);
                v___f_7270_ = leanh::lean_alloc_closure(
                    l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_7270_, 0, v___x_7268_);
                v___f_7271_ = leanh::lean_alloc_closure(
                    l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_7271_, 0, v___x_7268_);
                v___f_7272_ = leanh::lean_alloc_closure(
                    l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_7272_, 0, v___x_7268_);
                v___x_7273_ =
                    leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
                leanh::lean_closure_set(v___x_7273_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_7273_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_7273_, 2, v___x_7268_);
                v___x_7274_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7274_, 0, v___x_7273_);
                leanh::lean_ctor_set(v___x_7274_, 1, v___f_7269_);
                v___x_7275_ =
                    leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
                leanh::lean_closure_set(v___x_7275_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_7275_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_7275_, 2, v___x_7268_);
                v___x_7276_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_7276_, 0, v___x_7274_);
                leanh::lean_ctor_set(v___x_7276_, 1, v___x_7275_);
                leanh::lean_ctor_set(v___x_7276_, 2, v___f_7270_);
                leanh::lean_ctor_set(v___x_7276_, 3, v___f_7271_);
                leanh::lean_ctor_set(v___x_7276_, 4, v___f_7272_);
                v___x_7277_ =
                    leanh::lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
                leanh::lean_closure_set(v___x_7277_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_7277_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_7277_, 2, v___x_7268_);
                v___x_7278_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7278_, 0, v___x_7276_);
                leanh::lean_ctor_set(v___x_7278_, 1, v___x_7277_);
                v___x_7279_ = leanh::lean_box(0);
                v___x_7280_ = l_instInhabitedOfMonad___redArg(v___x_7278_, v___x_7279_);
                v___x_14557__overap_7281_ = lean_panic_fn_borrowed(v___x_7280_, v_msg_7239_);
                leanh::lean_dec(v___x_7280_);
                leanh::lean_inc(v___y_7242_);
                leanh::lean_inc_ref(v___y_7241_);
                v___x_7282_ = leanh::lean_apply_4(
                    v___x_14557__overap_7281_,
                    v___y_7240_,
                    v___y_7241_,
                    v___y_7242_,
                    leanh::lean_box(0),
                );
                return v___x_7282_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___boxed(
    mut v_msg_7289_: *mut leanh::LeanObject,
    mut v___y_7290_: *mut leanh::LeanObject,
    mut v___y_7291_: *mut leanh::LeanObject,
    mut v___y_7292_: *mut leanh::LeanObject,
    mut v___y_7293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7294_ =
        l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(
            v_msg_7289_,
            v___y_7290_,
            v___y_7291_,
            v___y_7292_,
        );
    leanh::lean_dec(v___y_7292_);
    leanh::lean_dec_ref(v___y_7291_);
    return v_res_7294_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(
    mut v_a_7295_: *mut leanh::LeanObject,
    mut v_x_7296_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_7297_: u8 = 0;
    let mut v_key_7298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7300_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_7296_) == 0 {
                    v___x_7297_ = 0;
                    return v___x_7297_;
                } else {
                    v_key_7298_ = leanh::lean_ctor_get(v_x_7296_, 0);
                    v_tail_7299_ = leanh::lean_ctor_get(v_x_7296_, 2);
                    v___x_7300_ = l_Lean_instBEqFVarId_beq(v_key_7298_, v_a_7295_);
                    if v___x_7300_ == 0 {
                        v_x_7296_ = v_tail_7299_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_7300_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg___boxed(
    mut v_a_7302_: *mut leanh::LeanObject,
    mut v_x_7303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7304_: u8 = 0;
    let mut v_r_7305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7304_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_7302_, v_x_7303_);
    leanh::lean_dec(v_x_7303_);
    leanh::lean_dec(v_a_7302_);
    v_r_7305_ = leanh::lean_box((v_res_7304_) as usize);
    return v_r_7305_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(
    mut v_x_7306_: *mut leanh::LeanObject,
    mut v_x_7307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_7308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7313_: u8 = 0;
    let mut v___x_7314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7315_: u64 = 0;
    let mut v___x_7316_: u64 = 0;
    let mut v___x_7317_: u64 = 0;
    let mut v_fold_7318_: u64 = 0;
    let mut v___x_7319_: u64 = 0;
    let mut v___x_7320_: u64 = 0;
    let mut v___x_7321_: u64 = 0;
    let mut v___x_7322_: usize = 0;
    let mut v___x_7323_: usize = 0;
    let mut v___x_7324_: usize = 0;
    let mut v___x_7325_: usize = 0;
    let mut v___x_7326_: usize = 0;
    let mut v___x_7327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7333_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_7307_) == 0 {
                    return v_x_7306_;
                } else {
                    v_key_7308_ = leanh::lean_ctor_get(v_x_7307_, 0);
                    v_value_7309_ = leanh::lean_ctor_get(v_x_7307_, 1);
                    v_tail_7310_ = leanh::lean_ctor_get(v_x_7307_, 2);
                    v_isSharedCheck_7333_ = (!leanh::lean_is_exclusive(v_x_7307_)) as u8;
                    if v_isSharedCheck_7333_ == 0 {
                        v___x_7312_ = v_x_7307_;
                        v_isShared_7313_ = v_isSharedCheck_7333_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_7310_);
                        leanh::lean_inc(v_value_7309_);
                        leanh::lean_inc(v_key_7308_);
                        leanh::lean_dec(v_x_7307_);
                        v___x_7312_ = leanh::lean_box(0);
                        v_isShared_7313_ = v_isSharedCheck_7333_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7314_ = lean_array_get_size(v_x_7306_);
                v___x_7315_ = l_Lean_instHashableFVarId_hash(v_key_7308_);
                v___x_7316_ = 32u64;
                v___x_7317_ = lean_uint64_shift_right(v___x_7315_, v___x_7316_);
                v_fold_7318_ = lean_uint64_xor(v___x_7315_, v___x_7317_);
                v___x_7319_ = 16u64;
                v___x_7320_ = lean_uint64_shift_right(v_fold_7318_, v___x_7319_);
                v___x_7321_ = lean_uint64_xor(v_fold_7318_, v___x_7320_);
                v___x_7322_ = lean_uint64_to_usize(v___x_7321_);
                v___x_7323_ = lean_usize_of_nat(v___x_7314_);
                v___x_7324_ = 1usize;
                v___x_7325_ = lean_usize_sub(v___x_7323_, v___x_7324_);
                v___x_7326_ = lean_usize_land(v___x_7322_, v___x_7325_);
                v___x_7327_ = lean_array_uget_borrowed(v_x_7306_, v___x_7326_);
                leanh::lean_inc(v___x_7327_);
                if v_isShared_7313_ == 0 {
                    leanh::lean_ctor_set(v___x_7312_, 2, v___x_7327_);
                    v___x_7329_ = v___x_7312_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7332_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7332_, 0, v_key_7308_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7332_, 1, v_value_7309_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7332_, 2, v___x_7327_);
                    v___x_7329_ = v_reuseFailAlloc_7332_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7330_ = lean_array_uset(v_x_7306_, v___x_7326_, v___x_7329_);
                v_x_7306_ = v___x_7330_;
                v_x_7307_ = v_tail_7310_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(
    mut v_i_7334_: *mut leanh::LeanObject,
    mut v_source_7335_: *mut leanh::LeanObject,
    mut v_target_7336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7338_: u8 = 0;
    let mut v_es_7339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_7341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_7342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7337_ = lean_array_get_size(v_source_7335_);
                v___x_7338_ = lean_nat_dec_lt(v_i_7334_, v___x_7337_);
                if v___x_7338_ == 0 {
                    leanh::lean_dec_ref(v_source_7335_);
                    leanh::lean_dec(v_i_7334_);
                    return v_target_7336_;
                } else {
                    v_es_7339_ = lean_array_fget(v_source_7335_, v_i_7334_);
                    v___x_7340_ = leanh::lean_box(0);
                    v_source_7341_ = lean_array_fset(v_source_7335_, v_i_7334_, v___x_7340_);
                    v_target_7342_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(v_target_7336_, v_es_7339_);
                    v___x_7343_ = leanh::lean_unsigned_to_nat(1);
                    v___x_7344_ = lean_nat_add(v_i_7334_, v___x_7343_);
                    leanh::lean_dec(v_i_7334_);
                    v_i_7334_ = v___x_7344_;
                    v_source_7335_ = v_source_7341_;
                    v_target_7336_ = v_target_7342_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(
    mut v_data_7346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_7349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7347_ = lean_array_get_size(v_data_7346_);
    v___x_7348_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_7349_ = lean_nat_mul(v___x_7347_, v___x_7348_);
    v___x_7350_ = leanh::lean_unsigned_to_nat(0);
    v___x_7351_ = leanh::lean_box(0);
    v___x_7352_ = lean_mk_array(v_nbuckets_7349_, v___x_7351_);
    v___x_7353_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(v___x_7350_, v_data_7346_, v___x_7352_);
    return v___x_7353_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(
    mut v_m_7354_: *mut leanh::LeanObject,
    mut v_a_7355_: *mut leanh::LeanObject,
    mut v_b_7356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_7357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_7358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7360_: u64 = 0;
    let mut v___x_7361_: u64 = 0;
    let mut v___x_7362_: u64 = 0;
    let mut v_fold_7363_: u64 = 0;
    let mut v___x_7364_: u64 = 0;
    let mut v___x_7365_: u64 = 0;
    let mut v___x_7366_: u64 = 0;
    let mut v___x_7367_: usize = 0;
    let mut v___x_7368_: usize = 0;
    let mut v___x_7369_: usize = 0;
    let mut v___x_7370_: usize = 0;
    let mut v___x_7371_: usize = 0;
    let mut v_bkt_7372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7373_: u8 = 0;
    let mut v___x_7375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7376_: u8 = 0;
    let mut v___x_7377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_7378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_7380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7386_: u8 = 0;
    let mut v_val_7387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7394_: u8 = 0;
    let mut v_unused_7395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_7357_ = leanh::lean_ctor_get(v_m_7354_, 0);
                v_buckets_7358_ = leanh::lean_ctor_get(v_m_7354_, 1);
                v___x_7359_ = lean_array_get_size(v_buckets_7358_);
                v___x_7360_ = l_Lean_instHashableFVarId_hash(v_a_7355_);
                v___x_7361_ = 32u64;
                v___x_7362_ = lean_uint64_shift_right(v___x_7360_, v___x_7361_);
                v_fold_7363_ = lean_uint64_xor(v___x_7360_, v___x_7362_);
                v___x_7364_ = 16u64;
                v___x_7365_ = lean_uint64_shift_right(v_fold_7363_, v___x_7364_);
                v___x_7366_ = lean_uint64_xor(v_fold_7363_, v___x_7365_);
                v___x_7367_ = lean_uint64_to_usize(v___x_7366_);
                v___x_7368_ = lean_usize_of_nat(v___x_7359_);
                v___x_7369_ = 1usize;
                v___x_7370_ = lean_usize_sub(v___x_7368_, v___x_7369_);
                v___x_7371_ = lean_usize_land(v___x_7367_, v___x_7370_);
                v_bkt_7372_ = lean_array_uget_borrowed(v_buckets_7358_, v___x_7371_);
                v___x_7373_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_7355_, v_bkt_7372_);
                if v___x_7373_ == 0 {
                    leanh::lean_inc_ref(v_buckets_7358_);
                    leanh::lean_inc(v_size_7357_);
                    v_isSharedCheck_7394_ = (!leanh::lean_is_exclusive(v_m_7354_)) as u8;
                    if v_isSharedCheck_7394_ == 0 {
                        v_unused_7395_ = leanh::lean_ctor_get(v_m_7354_, 1);
                        leanh::lean_dec(v_unused_7395_);
                        v_unused_7396_ = leanh::lean_ctor_get(v_m_7354_, 0);
                        leanh::lean_dec(v_unused_7396_);
                        v___x_7375_ = v_m_7354_;
                        v_isShared_7376_ = v_isSharedCheck_7394_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_7354_);
                        v___x_7375_ = leanh::lean_box(0);
                        v_isShared_7376_ = v_isSharedCheck_7394_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_7356_);
                    leanh::lean_dec(v_a_7355_);
                    return v_m_7354_;
                }
            }
            1 => {
                v___x_7377_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_7378_ = lean_nat_add(v_size_7357_, v___x_7377_);
                leanh::lean_dec(v_size_7357_);
                leanh::lean_inc(v_bkt_7372_);
                v___x_7379_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_7379_, 0, v_a_7355_);
                leanh::lean_ctor_set(v___x_7379_, 1, v_b_7356_);
                leanh::lean_ctor_set(v___x_7379_, 2, v_bkt_7372_);
                v_buckets_x27_7380_ = lean_array_uset(v_buckets_7358_, v___x_7371_, v___x_7379_);
                v___x_7381_ = leanh::lean_unsigned_to_nat(4);
                v___x_7382_ = lean_nat_mul(v_size_x27_7378_, v___x_7381_);
                v___x_7383_ = leanh::lean_unsigned_to_nat(3);
                v___x_7384_ = lean_nat_div(v___x_7382_, v___x_7383_);
                leanh::lean_dec(v___x_7382_);
                v___x_7385_ = lean_array_get_size(v_buckets_x27_7380_);
                v___x_7386_ = lean_nat_dec_le(v___x_7384_, v___x_7385_);
                leanh::lean_dec(v___x_7384_);
                if v___x_7386_ == 0 {
                    v_val_7387_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_buckets_x27_7380_);
                    if v_isShared_7376_ == 0 {
                        leanh::lean_ctor_set(v___x_7375_, 1, v_val_7387_);
                        leanh::lean_ctor_set(v___x_7375_, 0, v_size_x27_7378_);
                        v___x_7389_ = v___x_7375_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7390_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7390_, 0, v_size_x27_7378_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7390_, 1, v_val_7387_);
                        v___x_7389_ = v_reuseFailAlloc_7390_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_7376_ == 0 {
                        leanh::lean_ctor_set(v___x_7375_, 1, v_buckets_x27_7380_);
                        leanh::lean_ctor_set(v___x_7375_, 0, v_size_x27_7378_);
                        v___x_7392_ = v___x_7375_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7393_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7393_, 0, v_size_x27_7378_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7393_, 1, v_buckets_x27_7380_);
                        v___x_7392_ = v_reuseFailAlloc_7393_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7389_;
            }
            3 => {
                return v___x_7392_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(
    mut v_m_7397_: *mut leanh::LeanObject,
    mut v_a_7398_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_7399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7401_: u64 = 0;
    let mut v___x_7402_: u64 = 0;
    let mut v___x_7403_: u64 = 0;
    let mut v_fold_7404_: u64 = 0;
    let mut v___x_7405_: u64 = 0;
    let mut v___x_7406_: u64 = 0;
    let mut v___x_7407_: u64 = 0;
    let mut v___x_7408_: usize = 0;
    let mut v___x_7409_: usize = 0;
    let mut v___x_7410_: usize = 0;
    let mut v___x_7411_: usize = 0;
    let mut v___x_7412_: usize = 0;
    let mut v___x_7413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7414_: u8 = 0;
    v_buckets_7399_ = leanh::lean_ctor_get(v_m_7397_, 1);
    v___x_7400_ = lean_array_get_size(v_buckets_7399_);
    v___x_7401_ = l_Lean_instHashableFVarId_hash(v_a_7398_);
    v___x_7402_ = 32u64;
    v___x_7403_ = lean_uint64_shift_right(v___x_7401_, v___x_7402_);
    v_fold_7404_ = lean_uint64_xor(v___x_7401_, v___x_7403_);
    v___x_7405_ = 16u64;
    v___x_7406_ = lean_uint64_shift_right(v_fold_7404_, v___x_7405_);
    v___x_7407_ = lean_uint64_xor(v_fold_7404_, v___x_7406_);
    v___x_7408_ = lean_uint64_to_usize(v___x_7407_);
    v___x_7409_ = lean_usize_of_nat(v___x_7400_);
    v___x_7410_ = 1usize;
    v___x_7411_ = lean_usize_sub(v___x_7409_, v___x_7410_);
    v___x_7412_ = lean_usize_land(v___x_7408_, v___x_7411_);
    v___x_7413_ = lean_array_uget_borrowed(v_buckets_7399_, v___x_7412_);
    v___x_7414_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_7398_, v___x_7413_);
    return v___x_7414_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg___boxed(
    mut v_m_7415_: *mut leanh::LeanObject,
    mut v_a_7416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7417_: u8 = 0;
    let mut v_r_7418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7417_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_m_7415_, v_a_7416_);
    leanh::lean_dec(v_a_7416_);
    leanh::lean_dec_ref(v_m_7415_);
    v_r_7418_ = leanh::lean_box((v_res_7417_) as usize);
    return v_r_7418_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(
    mut v_a_7419_: *mut leanh::LeanObject,
    mut v_x_7420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_7422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7425_: u8 = 0;
    let mut v___x_7427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_7420_) == 0 {
                    v___x_7421_ = leanh::lean_box(0);
                    return v___x_7421_;
                } else {
                    v_key_7422_ = leanh::lean_ctor_get(v_x_7420_, 0);
                    v_value_7423_ = leanh::lean_ctor_get(v_x_7420_, 1);
                    v_tail_7424_ = leanh::lean_ctor_get(v_x_7420_, 2);
                    v___x_7425_ = lean_expr_eqv(v_key_7422_, v_a_7419_);
                    if v___x_7425_ == 0 {
                        v_x_7420_ = v_tail_7424_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_7423_);
                        v___x_7427_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_7427_, 0, v_value_7423_);
                        return v___x_7427_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg___boxed(
    mut v_a_7428_: *mut leanh::LeanObject,
    mut v_x_7429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7430_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_7428_, v_x_7429_);
    leanh::lean_dec(v_x_7429_);
    leanh::lean_dec_ref(v_a_7428_);
    return v_res_7430_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(
    mut v_m_7431_: *mut leanh::LeanObject,
    mut v_a_7432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_7433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7435_: u64 = 0;
    let mut v___x_7436_: u64 = 0;
    let mut v___x_7437_: u64 = 0;
    let mut v_fold_7438_: u64 = 0;
    let mut v___x_7439_: u64 = 0;
    let mut v___x_7440_: u64 = 0;
    let mut v___x_7441_: u64 = 0;
    let mut v___x_7442_: usize = 0;
    let mut v___x_7443_: usize = 0;
    let mut v___x_7444_: usize = 0;
    let mut v___x_7445_: usize = 0;
    let mut v___x_7446_: usize = 0;
    let mut v___x_7447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_7433_ = leanh::lean_ctor_get(v_m_7431_, 1);
    v___x_7434_ = lean_array_get_size(v_buckets_7433_);
    v___x_7435_ = l_Lean_Expr_hash(v_a_7432_);
    v___x_7436_ = 32u64;
    v___x_7437_ = lean_uint64_shift_right(v___x_7435_, v___x_7436_);
    v_fold_7438_ = lean_uint64_xor(v___x_7435_, v___x_7437_);
    v___x_7439_ = 16u64;
    v___x_7440_ = lean_uint64_shift_right(v_fold_7438_, v___x_7439_);
    v___x_7441_ = lean_uint64_xor(v_fold_7438_, v___x_7440_);
    v___x_7442_ = lean_uint64_to_usize(v___x_7441_);
    v___x_7443_ = lean_usize_of_nat(v___x_7434_);
    v___x_7444_ = 1usize;
    v___x_7445_ = lean_usize_sub(v___x_7443_, v___x_7444_);
    v___x_7446_ = lean_usize_land(v___x_7442_, v___x_7445_);
    v___x_7447_ = lean_array_uget_borrowed(v_buckets_7433_, v___x_7446_);
    v___x_7448_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_7432_, v___x_7447_);
    return v___x_7448_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg___boxed(
    mut v_m_7449_: *mut leanh::LeanObject,
    mut v_a_7450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7451_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v_m_7449_, v_a_7450_);
    leanh::lean_dec_ref(v_a_7450_);
    leanh::lean_dec_ref(v_m_7449_);
    return v_res_7451_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(
    mut v_a_7452_: *mut leanh::LeanObject,
    mut v_b_7453_: *mut leanh::LeanObject,
    mut v_x_7454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_7455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7460_: u8 = 0;
    let mut v___x_7461_: u8 = 0;
    let mut v___x_7462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7469_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_7454_) == 0 {
                    leanh::lean_dec(v_b_7453_);
                    leanh::lean_dec_ref(v_a_7452_);
                    return v_x_7454_;
                } else {
                    v_key_7455_ = leanh::lean_ctor_get(v_x_7454_, 0);
                    v_value_7456_ = leanh::lean_ctor_get(v_x_7454_, 1);
                    v_tail_7457_ = leanh::lean_ctor_get(v_x_7454_, 2);
                    v_isSharedCheck_7469_ = (!leanh::lean_is_exclusive(v_x_7454_)) as u8;
                    if v_isSharedCheck_7469_ == 0 {
                        v___x_7459_ = v_x_7454_;
                        v_isShared_7460_ = v_isSharedCheck_7469_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_7457_);
                        leanh::lean_inc(v_value_7456_);
                        leanh::lean_inc(v_key_7455_);
                        leanh::lean_dec(v_x_7454_);
                        v___x_7459_ = leanh::lean_box(0);
                        v_isShared_7460_ = v_isSharedCheck_7469_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7461_ = lean_expr_eqv(v_key_7455_, v_a_7452_);
                if v___x_7461_ == 0 {
                    v___x_7462_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_7452_, v_b_7453_, v_tail_7457_);
                    if v_isShared_7460_ == 0 {
                        leanh::lean_ctor_set(v___x_7459_, 2, v___x_7462_);
                        v___x_7464_ = v___x_7459_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7465_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7465_, 0, v_key_7455_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7465_, 1, v_value_7456_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7465_, 2, v___x_7462_);
                        v___x_7464_ = v_reuseFailAlloc_7465_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_7456_);
                    leanh::lean_dec(v_key_7455_);
                    if v_isShared_7460_ == 0 {
                        leanh::lean_ctor_set(v___x_7459_, 1, v_b_7453_);
                        leanh::lean_ctor_set(v___x_7459_, 0, v_a_7452_);
                        v___x_7467_ = v___x_7459_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7468_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7468_, 0, v_a_7452_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7468_, 1, v_b_7453_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7468_, 2, v_tail_7457_);
                        v___x_7467_ = v_reuseFailAlloc_7468_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7464_;
            }
            3 => {
                return v___x_7467_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(
    mut v_x_7470_: *mut leanh::LeanObject,
    mut v_x_7471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_7472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7477_: u8 = 0;
    let mut v___x_7478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7479_: u64 = 0;
    let mut v___x_7480_: u64 = 0;
    let mut v___x_7481_: u64 = 0;
    let mut v_fold_7482_: u64 = 0;
    let mut v___x_7483_: u64 = 0;
    let mut v___x_7484_: u64 = 0;
    let mut v___x_7485_: u64 = 0;
    let mut v___x_7486_: usize = 0;
    let mut v___x_7487_: usize = 0;
    let mut v___x_7488_: usize = 0;
    let mut v___x_7489_: usize = 0;
    let mut v___x_7490_: usize = 0;
    let mut v___x_7491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7497_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_7471_) == 0 {
                    return v_x_7470_;
                } else {
                    v_key_7472_ = leanh::lean_ctor_get(v_x_7471_, 0);
                    v_value_7473_ = leanh::lean_ctor_get(v_x_7471_, 1);
                    v_tail_7474_ = leanh::lean_ctor_get(v_x_7471_, 2);
                    v_isSharedCheck_7497_ = (!leanh::lean_is_exclusive(v_x_7471_)) as u8;
                    if v_isSharedCheck_7497_ == 0 {
                        v___x_7476_ = v_x_7471_;
                        v_isShared_7477_ = v_isSharedCheck_7497_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_7474_);
                        leanh::lean_inc(v_value_7473_);
                        leanh::lean_inc(v_key_7472_);
                        leanh::lean_dec(v_x_7471_);
                        v___x_7476_ = leanh::lean_box(0);
                        v_isShared_7477_ = v_isSharedCheck_7497_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7478_ = lean_array_get_size(v_x_7470_);
                v___x_7479_ = l_Lean_Expr_hash(v_key_7472_);
                v___x_7480_ = 32u64;
                v___x_7481_ = lean_uint64_shift_right(v___x_7479_, v___x_7480_);
                v_fold_7482_ = lean_uint64_xor(v___x_7479_, v___x_7481_);
                v___x_7483_ = 16u64;
                v___x_7484_ = lean_uint64_shift_right(v_fold_7482_, v___x_7483_);
                v___x_7485_ = lean_uint64_xor(v_fold_7482_, v___x_7484_);
                v___x_7486_ = lean_uint64_to_usize(v___x_7485_);
                v___x_7487_ = lean_usize_of_nat(v___x_7478_);
                v___x_7488_ = 1usize;
                v___x_7489_ = lean_usize_sub(v___x_7487_, v___x_7488_);
                v___x_7490_ = lean_usize_land(v___x_7486_, v___x_7489_);
                v___x_7491_ = lean_array_uget_borrowed(v_x_7470_, v___x_7490_);
                leanh::lean_inc(v___x_7491_);
                if v_isShared_7477_ == 0 {
                    leanh::lean_ctor_set(v___x_7476_, 2, v___x_7491_);
                    v___x_7493_ = v___x_7476_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7496_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7496_, 0, v_key_7472_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7496_, 1, v_value_7473_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7496_, 2, v___x_7491_);
                    v___x_7493_ = v_reuseFailAlloc_7496_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7494_ = lean_array_uset(v_x_7470_, v___x_7490_, v___x_7493_);
                v_x_7470_ = v___x_7494_;
                v_x_7471_ = v_tail_7474_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(
    mut v_i_7498_: *mut leanh::LeanObject,
    mut v_source_7499_: *mut leanh::LeanObject,
    mut v_target_7500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7502_: u8 = 0;
    let mut v_es_7503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_7505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_7506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7501_ = lean_array_get_size(v_source_7499_);
                v___x_7502_ = lean_nat_dec_lt(v_i_7498_, v___x_7501_);
                if v___x_7502_ == 0 {
                    leanh::lean_dec_ref(v_source_7499_);
                    leanh::lean_dec(v_i_7498_);
                    return v_target_7500_;
                } else {
                    v_es_7503_ = lean_array_fget(v_source_7499_, v_i_7498_);
                    v___x_7504_ = leanh::lean_box(0);
                    v_source_7505_ = lean_array_fset(v_source_7499_, v_i_7498_, v___x_7504_);
                    v_target_7506_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(v_target_7500_, v_es_7503_);
                    v___x_7507_ = leanh::lean_unsigned_to_nat(1);
                    v___x_7508_ = lean_nat_add(v_i_7498_, v___x_7507_);
                    leanh::lean_dec(v_i_7498_);
                    v_i_7498_ = v___x_7508_;
                    v_source_7499_ = v_source_7505_;
                    v_target_7500_ = v_target_7506_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(
    mut v_data_7510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_7513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7511_ = lean_array_get_size(v_data_7510_);
    v___x_7512_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_7513_ = lean_nat_mul(v___x_7511_, v___x_7512_);
    v___x_7514_ = leanh::lean_unsigned_to_nat(0);
    v___x_7515_ = leanh::lean_box(0);
    v___x_7516_ = lean_mk_array(v_nbuckets_7513_, v___x_7515_);
    v___x_7517_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(v___x_7514_, v_data_7510_, v___x_7516_);
    return v___x_7517_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(
    mut v_a_7518_: *mut leanh::LeanObject,
    mut v_x_7519_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_7520_: u8 = 0;
    let mut v_key_7521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7523_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_7519_) == 0 {
                    v___x_7520_ = 0;
                    return v___x_7520_;
                } else {
                    v_key_7521_ = leanh::lean_ctor_get(v_x_7519_, 0);
                    v_tail_7522_ = leanh::lean_ctor_get(v_x_7519_, 2);
                    v___x_7523_ = lean_expr_eqv(v_key_7521_, v_a_7518_);
                    if v___x_7523_ == 0 {
                        v_x_7519_ = v_tail_7522_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_7523_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg___boxed(
    mut v_a_7525_: *mut leanh::LeanObject,
    mut v_x_7526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7527_: u8 = 0;
    let mut v_r_7528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7527_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_7525_, v_x_7526_);
    leanh::lean_dec(v_x_7526_);
    leanh::lean_dec_ref(v_a_7525_);
    v_r_7528_ = leanh::lean_box((v_res_7527_) as usize);
    return v_r_7528_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(
    mut v_m_7529_: *mut leanh::LeanObject,
    mut v_a_7530_: *mut leanh::LeanObject,
    mut v_b_7531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_7532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_7533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7536_: u8 = 0;
    let mut v___x_7537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7538_: u64 = 0;
    let mut v___x_7539_: u64 = 0;
    let mut v___x_7540_: u64 = 0;
    let mut v_fold_7541_: u64 = 0;
    let mut v___x_7542_: u64 = 0;
    let mut v___x_7543_: u64 = 0;
    let mut v___x_7544_: u64 = 0;
    let mut v___x_7545_: usize = 0;
    let mut v___x_7546_: usize = 0;
    let mut v___x_7547_: usize = 0;
    let mut v___x_7548_: usize = 0;
    let mut v___x_7549_: usize = 0;
    let mut v_bkt_7550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7551_: u8 = 0;
    let mut v___x_7552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_7553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_7555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7561_: u8 = 0;
    let mut v_val_7562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_7570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7576_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_7532_ = leanh::lean_ctor_get(v_m_7529_, 0);
                v_buckets_7533_ = leanh::lean_ctor_get(v_m_7529_, 1);
                v_isSharedCheck_7576_ = (!leanh::lean_is_exclusive(v_m_7529_)) as u8;
                if v_isSharedCheck_7576_ == 0 {
                    v___x_7535_ = v_m_7529_;
                    v_isShared_7536_ = v_isSharedCheck_7576_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_7533_);
                    leanh::lean_inc(v_size_7532_);
                    leanh::lean_dec(v_m_7529_);
                    v___x_7535_ = leanh::lean_box(0);
                    v_isShared_7536_ = v_isSharedCheck_7576_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7537_ = lean_array_get_size(v_buckets_7533_);
                v___x_7538_ = l_Lean_Expr_hash(v_a_7530_);
                v___x_7539_ = 32u64;
                v___x_7540_ = lean_uint64_shift_right(v___x_7538_, v___x_7539_);
                v_fold_7541_ = lean_uint64_xor(v___x_7538_, v___x_7540_);
                v___x_7542_ = 16u64;
                v___x_7543_ = lean_uint64_shift_right(v_fold_7541_, v___x_7542_);
                v___x_7544_ = lean_uint64_xor(v_fold_7541_, v___x_7543_);
                v___x_7545_ = lean_uint64_to_usize(v___x_7544_);
                v___x_7546_ = lean_usize_of_nat(v___x_7537_);
                v___x_7547_ = 1usize;
                v___x_7548_ = lean_usize_sub(v___x_7546_, v___x_7547_);
                v___x_7549_ = lean_usize_land(v___x_7545_, v___x_7548_);
                v_bkt_7550_ = lean_array_uget_borrowed(v_buckets_7533_, v___x_7549_);
                v___x_7551_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_7530_, v_bkt_7550_);
                if v___x_7551_ == 0 {
                    v___x_7552_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_7553_ = lean_nat_add(v_size_7532_, v___x_7552_);
                    leanh::lean_dec(v_size_7532_);
                    leanh::lean_inc(v_bkt_7550_);
                    v___x_7554_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_7554_, 0, v_a_7530_);
                    leanh::lean_ctor_set(v___x_7554_, 1, v_b_7531_);
                    leanh::lean_ctor_set(v___x_7554_, 2, v_bkt_7550_);
                    v_buckets_x27_7555_ =
                        lean_array_uset(v_buckets_7533_, v___x_7549_, v___x_7554_);
                    v___x_7556_ = leanh::lean_unsigned_to_nat(4);
                    v___x_7557_ = lean_nat_mul(v_size_x27_7553_, v___x_7556_);
                    v___x_7558_ = leanh::lean_unsigned_to_nat(3);
                    v___x_7559_ = lean_nat_div(v___x_7557_, v___x_7558_);
                    leanh::lean_dec(v___x_7557_);
                    v___x_7560_ = lean_array_get_size(v_buckets_x27_7555_);
                    v___x_7561_ = lean_nat_dec_le(v___x_7559_, v___x_7560_);
                    leanh::lean_dec(v___x_7559_);
                    if v___x_7561_ == 0 {
                        v_val_7562_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(v_buckets_x27_7555_);
                        if v_isShared_7536_ == 0 {
                            leanh::lean_ctor_set(v___x_7535_, 1, v_val_7562_);
                            leanh::lean_ctor_set(v___x_7535_, 0, v_size_x27_7553_);
                            v___x_7564_ = v___x_7535_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_7565_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_7565_,
                                0,
                                v_size_x27_7553_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_7565_, 1, v_val_7562_);
                            v___x_7564_ = v_reuseFailAlloc_7565_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_7536_ == 0 {
                            leanh::lean_ctor_set(v___x_7535_, 1, v_buckets_x27_7555_);
                            leanh::lean_ctor_set(v___x_7535_, 0, v_size_x27_7553_);
                            v___x_7567_ = v___x_7535_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_7568_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_7568_,
                                0,
                                v_size_x27_7553_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_7568_,
                                1,
                                v_buckets_x27_7555_,
                            );
                            v___x_7567_ = v_reuseFailAlloc_7568_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_7550_);
                    v___x_7569_ = leanh::lean_box(0);
                    v_buckets_x27_7570_ =
                        lean_array_uset(v_buckets_7533_, v___x_7549_, v___x_7569_);
                    v___x_7571_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_7530_, v_b_7531_, v_bkt_7550_);
                    v___x_7572_ = lean_array_uset(v_buckets_x27_7570_, v___x_7549_, v___x_7571_);
                    if v_isShared_7536_ == 0 {
                        leanh::lean_ctor_set(v___x_7535_, 1, v___x_7572_);
                        v___x_7574_ = v___x_7535_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_7575_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7575_, 0, v_size_7532_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7575_, 1, v___x_7572_);
                        v___x_7574_ = v_reuseFailAlloc_7575_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7564_;
            }
            3 => {
                return v___x_7567_;
            }
            4 => {
                return v___x_7574_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(
    mut v_g_7577_: *mut leanh::LeanObject,
    mut v_e_7578_: *mut leanh::LeanObject,
    mut v_a_7579_: *mut leanh::LeanObject,
    mut v___y_7580_: *mut leanh::LeanObject,
    mut v___y_7581_: *mut leanh::LeanObject,
    mut v___y_7582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_7585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7603_: u8 = 0;
    let mut v_d_7605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_7606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7612_: u8 = 0;
    let mut v___x_7613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_7617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_7618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_7619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_7620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_7623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_7631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_7632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_7637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_7639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7645_: u8 = 0;
    let mut v_a_7646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7649_: u8 = 0;
    let mut v___x_7651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7653_: u8 = 0;
    let mut v_val_7654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7657_: u8 = 0;
    let mut v___x_7658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7662_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7595_ = lean_st_ref_get(v_a_7579_);
                v___x_7596_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v___x_7595_, v_e_7578_);
                leanh::lean_dec(v___x_7595_);
                if leanh::lean_obj_tag(v___x_7596_) == 0 {
                    leanh::lean_inc_ref(v_g_7577_);
                    leanh::lean_inc(v___y_7582_);
                    leanh::lean_inc_ref(v___y_7581_);
                    leanh::lean_inc_ref(v_e_7578_);
                    v___x_7597_ = leanh::lean_apply_5(
                        v_g_7577_,
                        v_e_7578_,
                        v___y_7580_,
                        v___y_7581_,
                        v___y_7582_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_7597_) == 0 {
                        v_a_7598_ = leanh::lean_ctor_get(v___x_7597_, 0);
                        leanh::lean_inc(v_a_7598_);
                        leanh::lean_dec_ref_known(v___x_7597_, 1);
                        v_fst_7599_ = leanh::lean_ctor_get(v_a_7598_, 0);
                        v_snd_7600_ = leanh::lean_ctor_get(v_a_7598_, 1);
                        v_isSharedCheck_7645_ = (!leanh::lean_is_exclusive(v_a_7598_)) as u8;
                        if v_isSharedCheck_7645_ == 0 {
                            v___x_7602_ = v_a_7598_;
                            v_isShared_7603_ = v_isSharedCheck_7645_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_7600_);
                            leanh::lean_inc(v_fst_7599_);
                            leanh::lean_dec(v_a_7598_);
                            v___x_7602_ = leanh::lean_box(0);
                            v_isShared_7603_ = v_isSharedCheck_7645_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_7578_);
                        leanh::lean_dec_ref(v_g_7577_);
                        v_a_7646_ = leanh::lean_ctor_get(v___x_7597_, 0);
                        v_isSharedCheck_7653_ =
                            (!leanh::lean_is_exclusive(v___x_7597_)) as u8;
                        if v_isSharedCheck_7653_ == 0 {
                            v___x_7648_ = v___x_7597_;
                            v_isShared_7649_ = v_isSharedCheck_7653_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7646_);
                            leanh::lean_dec(v___x_7597_);
                            v___x_7648_ = leanh::lean_box(0);
                            v_isShared_7649_ = v_isSharedCheck_7653_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_7578_);
                    leanh::lean_dec_ref(v_g_7577_);
                    v_val_7654_ = leanh::lean_ctor_get(v___x_7596_, 0);
                    v_isSharedCheck_7662_ = (!leanh::lean_is_exclusive(v___x_7596_)) as u8;
                    if v_isSharedCheck_7662_ == 0 {
                        v___x_7656_ = v___x_7596_;
                        v_isShared_7657_ = v_isSharedCheck_7662_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_7654_);
                        leanh::lean_dec(v___x_7596_);
                        v___x_7656_ = leanh::lean_box(0);
                        v_isShared_7657_ = v_isSharedCheck_7662_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7587_ = lean_st_ref_take(v_a_7579_);
                v___x_7588_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(v___x_7587_, v_e_7578_, v_fst_7586_);
                v___x_7589_ = lean_st_ref_set(v_a_7579_, v___x_7588_);
                v___x_7590_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7590_, 0, v_a_7585_);
                return v___x_7590_;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_7592_) == 0 {
                    v_a_7593_ = leanh::lean_ctor_get(v___y_7592_, 0);
                    leanh::lean_inc(v_a_7593_);
                    leanh::lean_dec_ref_known(v___y_7592_, 1);
                    v_fst_7594_ = leanh::lean_ctor_get(v_a_7593_, 0);
                    leanh::lean_inc(v_fst_7594_);
                    v_a_7585_ = v_a_7593_;
                    v_fst_7586_ = v_fst_7594_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_e_7578_);
                    return v___y_7592_;
                }
            }
            3 => {
                v___x_7612_ = (leanh::lean_unbox(v_fst_7599_) as u8);
                leanh::lean_dec(v_fst_7599_);
                if v___x_7612_ == 0 {
                    leanh::lean_dec_ref(v_g_7577_);
                    v___x_7613_ = leanh::lean_box(0);
                    if v_isShared_7603_ == 0 {
                        leanh::lean_ctor_set(v___x_7602_, 0, v___x_7613_);
                        v___x_7615_ = v___x_7602_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_7616_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7616_, 0, v___x_7613_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7616_, 1, v_snd_7600_);
                        v___x_7615_ = v_reuseFailAlloc_7616_;
                        state = 5;
                        continue;
                    }
                } else {
                    match leanh::lean_obj_tag(v_e_7578_) {
                        7 => {
                            leanh::lean_del_object(v___x_7602_);
                            v_binderType_7617_ = leanh::lean_ctor_get(v_e_7578_, 1);
                            v_body_7618_ = leanh::lean_ctor_get(v_e_7578_, 2);
                            leanh::lean_inc_ref(v_body_7618_);
                            leanh::lean_inc_ref(v_binderType_7617_);
                            v_d_7605_ = v_binderType_7617_;
                            v_b_7606_ = v_body_7618_;
                            v___y_7607_ = v_a_7579_;
                            state = 4;
                            continue;
                        }
                        6 => {
                            leanh::lean_del_object(v___x_7602_);
                            v_binderType_7619_ = leanh::lean_ctor_get(v_e_7578_, 1);
                            v_body_7620_ = leanh::lean_ctor_get(v_e_7578_, 2);
                            leanh::lean_inc_ref(v_body_7620_);
                            leanh::lean_inc_ref(v_binderType_7619_);
                            v_d_7605_ = v_binderType_7619_;
                            v_b_7606_ = v_body_7620_;
                            v___y_7607_ = v_a_7579_;
                            state = 4;
                            continue;
                        }
                        8 => {
                            leanh::lean_del_object(v___x_7602_);
                            v_type_7621_ = leanh::lean_ctor_get(v_e_7578_, 1);
                            v_value_7622_ = leanh::lean_ctor_get(v_e_7578_, 2);
                            v_body_7623_ = leanh::lean_ctor_get(v_e_7578_, 3);
                            leanh::lean_inc_ref(v_type_7621_);
                            leanh::lean_inc_ref(v_g_7577_);
                            v___x_7624_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_7577_, v_type_7621_, v_a_7579_, v_snd_7600_, v___y_7581_, v___y_7582_);
                            if leanh::lean_obj_tag(v___x_7624_) == 0 {
                                v_a_7625_ = leanh::lean_ctor_get(v___x_7624_, 0);
                                leanh::lean_inc(v_a_7625_);
                                leanh::lean_dec_ref_known(v___x_7624_, 1);
                                v_snd_7626_ = leanh::lean_ctor_get(v_a_7625_, 1);
                                leanh::lean_inc(v_snd_7626_);
                                leanh::lean_dec(v_a_7625_);
                                leanh::lean_inc_ref(v_value_7622_);
                                leanh::lean_inc_ref(v_g_7577_);
                                v___x_7627_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_7577_, v_value_7622_, v_a_7579_, v_snd_7626_, v___y_7581_, v___y_7582_);
                                if leanh::lean_obj_tag(v___x_7627_) == 0 {
                                    v_a_7628_ = leanh::lean_ctor_get(v___x_7627_, 0);
                                    leanh::lean_inc(v_a_7628_);
                                    leanh::lean_dec_ref_known(v___x_7627_, 1);
                                    v_snd_7629_ = leanh::lean_ctor_get(v_a_7628_, 1);
                                    leanh::lean_inc(v_snd_7629_);
                                    leanh::lean_dec(v_a_7628_);
                                    leanh::lean_inc_ref(v_body_7623_);
                                    v___x_7630_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_7577_, v_body_7623_, v_a_7579_, v_snd_7629_, v___y_7581_, v___y_7582_);
                                    v___y_7592_ = v___x_7630_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v_g_7577_);
                                    v___y_7592_ = v___x_7627_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_g_7577_);
                                v___y_7592_ = v___x_7624_;
                                state = 2;
                                continue;
                            }
                        }
                        5 => {
                            leanh::lean_del_object(v___x_7602_);
                            v_fn_7631_ = leanh::lean_ctor_get(v_e_7578_, 0);
                            v_arg_7632_ = leanh::lean_ctor_get(v_e_7578_, 1);
                            leanh::lean_inc_ref(v_fn_7631_);
                            leanh::lean_inc_ref(v_g_7577_);
                            v___x_7633_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_7577_, v_fn_7631_, v_a_7579_, v_snd_7600_, v___y_7581_, v___y_7582_);
                            if leanh::lean_obj_tag(v___x_7633_) == 0 {
                                v_a_7634_ = leanh::lean_ctor_get(v___x_7633_, 0);
                                leanh::lean_inc(v_a_7634_);
                                leanh::lean_dec_ref_known(v___x_7633_, 1);
                                v_snd_7635_ = leanh::lean_ctor_get(v_a_7634_, 1);
                                leanh::lean_inc(v_snd_7635_);
                                leanh::lean_dec(v_a_7634_);
                                leanh::lean_inc_ref(v_arg_7632_);
                                v___x_7636_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_7577_, v_arg_7632_, v_a_7579_, v_snd_7635_, v___y_7581_, v___y_7582_);
                                v___y_7592_ = v___x_7636_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_g_7577_);
                                v___y_7592_ = v___x_7633_;
                                state = 2;
                                continue;
                            }
                        }
                        10 => {
                            leanh::lean_del_object(v___x_7602_);
                            v_expr_7637_ = leanh::lean_ctor_get(v_e_7578_, 1);
                            leanh::lean_inc_ref(v_expr_7637_);
                            v___x_7638_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_7577_, v_expr_7637_, v_a_7579_, v_snd_7600_, v___y_7581_, v___y_7582_);
                            v___y_7592_ = v___x_7638_;
                            state = 2;
                            continue;
                        }
                        11 => {
                            leanh::lean_del_object(v___x_7602_);
                            v_struct_7639_ = leanh::lean_ctor_get(v_e_7578_, 2);
                            leanh::lean_inc_ref(v_struct_7639_);
                            v___x_7640_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_7577_, v_struct_7639_, v_a_7579_, v_snd_7600_, v___y_7581_, v___y_7582_);
                            v___y_7592_ = v___x_7640_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            leanh::lean_dec_ref(v_g_7577_);
                            v___x_7641_ = leanh::lean_box(0);
                            if v_isShared_7603_ == 0 {
                                leanh::lean_ctor_set(v___x_7602_, 0, v___x_7641_);
                                v___x_7643_ = v___x_7602_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_7644_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_7644_, 0, v___x_7641_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_7644_, 1, v_snd_7600_);
                                v___x_7643_ = v_reuseFailAlloc_7644_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                }
            }
            4 => {
                leanh::lean_inc_ref(v_g_7577_);
                v___x_7608_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_7577_, v_d_7605_, v___y_7607_, v_snd_7600_, v___y_7581_, v___y_7582_);
                if leanh::lean_obj_tag(v___x_7608_) == 0 {
                    v_a_7609_ = leanh::lean_ctor_get(v___x_7608_, 0);
                    leanh::lean_inc(v_a_7609_);
                    leanh::lean_dec_ref_known(v___x_7608_, 1);
                    v_snd_7610_ = leanh::lean_ctor_get(v_a_7609_, 1);
                    leanh::lean_inc(v_snd_7610_);
                    leanh::lean_dec(v_a_7609_);
                    v___x_7611_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_7577_, v_b_7606_, v___y_7607_, v_snd_7610_, v___y_7581_, v___y_7582_);
                    v___y_7592_ = v___x_7611_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_b_7606_);
                    leanh::lean_dec_ref(v_g_7577_);
                    v___y_7592_ = v___x_7608_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v_a_7585_ = v___x_7615_;
                v_fst_7586_ = v___x_7613_;
                state = 1;
                continue;
            }
            6 => {
                v_a_7585_ = v___x_7643_;
                v_fst_7586_ = v___x_7641_;
                state = 1;
                continue;
            }
            7 => {
                if v_isShared_7649_ == 0 {
                    v___x_7651_ = v___x_7648_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7652_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7652_, 0, v_a_7646_);
                    v___x_7651_ = v_reuseFailAlloc_7652_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7651_;
            }
            9 => {
                v___x_7658_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7658_, 0, v_val_7654_);
                leanh::lean_ctor_set(v___x_7658_, 1, v___y_7580_);
                if v_isShared_7657_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_7656_, 0);
                    leanh::lean_ctor_set(v___x_7656_, 0, v___x_7658_);
                    v___x_7660_ = v___x_7656_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7661_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7661_, 0, v___x_7658_);
                    v___x_7660_ = v_reuseFailAlloc_7661_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7660_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___boxed(
    mut v_g_7663_: *mut leanh::LeanObject,
    mut v_e_7664_: *mut leanh::LeanObject,
    mut v_a_7665_: *mut leanh::LeanObject,
    mut v___y_7666_: *mut leanh::LeanObject,
    mut v___y_7667_: *mut leanh::LeanObject,
    mut v___y_7668_: *mut leanh::LeanObject,
    mut v___y_7669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7670_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_7663_, v_e_7664_, v_a_7665_, v___y_7666_, v___y_7667_, v___y_7668_);
    leanh::lean_dec(v___y_7668_);
    leanh::lean_dec_ref(v___y_7667_);
    leanh::lean_dec(v_a_7665_);
    return v_res_7670_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_7671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7671_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_7671_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_7672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7672_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0);
    v___x_7673_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_7673_, 0, v___x_7672_);
    return v___x_7673_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_7674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7674_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1);
    v___x_7675_ = leanh::lean_unsigned_to_nat(0);
    v___x_7676_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_7676_, 0, v___x_7675_);
    leanh::lean_ctor_set(v___x_7676_, 1, v___x_7675_);
    leanh::lean_ctor_set(v___x_7676_, 2, v___x_7675_);
    leanh::lean_ctor_set(v___x_7676_, 3, v___x_7675_);
    leanh::lean_ctor_set(v___x_7676_, 4, v___x_7674_);
    leanh::lean_ctor_set(v___x_7676_, 5, v___x_7674_);
    leanh::lean_ctor_set(v___x_7676_, 6, v___x_7674_);
    leanh::lean_ctor_set(v___x_7676_, 7, v___x_7674_);
    leanh::lean_ctor_set(v___x_7676_, 8, v___x_7674_);
    leanh::lean_ctor_set(v___x_7676_, 9, v___x_7674_);
    return v___x_7676_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_7677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7677_ = leanh::lean_unsigned_to_nat(32);
    v___x_7678_ = lean_mk_empty_array_with_capacity(v___x_7677_);
    v___x_7679_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_7679_, 0, v___x_7678_);
    return v___x_7679_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_7680_: usize = 0;
    let mut v___x_7681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7680_ = 5usize;
    v___x_7681_ = leanh::lean_unsigned_to_nat(0);
    v___x_7682_ = leanh::lean_unsigned_to_nat(32);
    v___x_7683_ = lean_mk_empty_array_with_capacity(v___x_7682_);
    v___x_7684_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3);
    v___x_7685_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_7685_, 0, v___x_7684_);
    leanh::lean_ctor_set(v___x_7685_, 1, v___x_7683_);
    leanh::lean_ctor_set(v___x_7685_, 2, v___x_7681_);
    leanh::lean_ctor_set(v___x_7685_, 3, v___x_7681_);
    leanh::lean_ctor_set_usize(v___x_7685_, 4, v___x_7680_);
    return v___x_7685_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_7686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7686_ = leanh::lean_box(1);
    v___x_7687_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4);
    v___x_7688_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1);
    v___x_7689_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_7689_, 0, v___x_7688_);
    leanh::lean_ctor_set(v___x_7689_, 1, v___x_7687_);
    leanh::lean_ctor_set(v___x_7689_, 2, v___x_7686_);
    return v___x_7689_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(
    mut v_msgData_7690_: *mut leanh::LeanObject,
    mut v___y_7691_: *mut leanh::LeanObject,
    mut v___y_7692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_7696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7694_ = lean_st_ref_get(v___y_7692_);
    v_env_7695_ = leanh::lean_ctor_get(v___x_7694_, 0);
    leanh::lean_inc_ref(v_env_7695_);
    leanh::lean_dec(v___x_7694_);
    v_options_7696_ = leanh::lean_ctor_get(v___y_7691_, 2);
    v___x_7697_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2);
    v___x_7698_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__5);
    leanh::lean_inc_ref(v_options_7696_);
    v___x_7699_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_7699_, 0, v_env_7695_);
    leanh::lean_ctor_set(v___x_7699_, 1, v___x_7697_);
    leanh::lean_ctor_set(v___x_7699_, 2, v___x_7698_);
    leanh::lean_ctor_set(v___x_7699_, 3, v_options_7696_);
    v___x_7700_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7700_, 0, v___x_7699_);
    leanh::lean_ctor_set(v___x_7700_, 1, v_msgData_7690_);
    v___x_7701_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_7701_, 0, v___x_7700_);
    return v___x_7701_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___boxed(
    mut v_msgData_7702_: *mut leanh::LeanObject,
    mut v___y_7703_: *mut leanh::LeanObject,
    mut v___y_7704_: *mut leanh::LeanObject,
    mut v___y_7705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7706_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msgData_7702_, v___y_7703_, v___y_7704_);
    leanh::lean_dec(v___y_7704_);
    leanh::lean_dec_ref(v___y_7703_);
    return v_res_7706_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(
    mut v_msg_7707_: *mut leanh::LeanObject,
    mut v___y_7708_: *mut leanh::LeanObject,
    mut v___y_7709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_7711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7716_: u8 = 0;
    let mut v___x_7717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7721_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_7711_ = leanh::lean_ctor_get(v___y_7708_, 5);
                v___x_7712_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_7707_, v___y_7708_, v___y_7709_);
                v_a_7713_ = leanh::lean_ctor_get(v___x_7712_, 0);
                v_isSharedCheck_7721_ = (!leanh::lean_is_exclusive(v___x_7712_)) as u8;
                if v_isSharedCheck_7721_ == 0 {
                    v___x_7715_ = v___x_7712_;
                    v_isShared_7716_ = v_isSharedCheck_7721_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_7713_);
                    leanh::lean_dec(v___x_7712_);
                    v___x_7715_ = leanh::lean_box(0);
                    v_isShared_7716_ = v_isSharedCheck_7721_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_7711_);
                v___x_7717_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7717_, 0, v_ref_7711_);
                leanh::lean_ctor_set(v___x_7717_, 1, v_a_7713_);
                if v_isShared_7716_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_7715_, 1);
                    leanh::lean_ctor_set(v___x_7715_, 0, v___x_7717_);
                    v___x_7719_ = v___x_7715_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7720_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7720_, 0, v___x_7717_);
                    v___x_7719_ = v_reuseFailAlloc_7720_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7719_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg___boxed(
    mut v_msg_7722_: *mut leanh::LeanObject,
    mut v___y_7723_: *mut leanh::LeanObject,
    mut v___y_7724_: *mut leanh::LeanObject,
    mut v___y_7725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7726_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v_msg_7722_, v___y_7723_, v___y_7724_);
    leanh::lean_dec(v___y_7724_);
    leanh::lean_dec_ref(v___y_7723_);
    return v_res_7726_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0()
-> f64 {
    let mut v___x_7727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7728_: f64 = 0.0;
    v___x_7727_ = leanh::lean_unsigned_to_nat(0);
    v___x_7728_ = lean_float_of_nat(v___x_7727_);
    return v___x_7728_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(
    mut v_cls_7732_: *mut leanh::LeanObject,
    mut v_msg_7733_: *mut leanh::LeanObject,
    mut v___y_7734_: *mut leanh::LeanObject,
    mut v___y_7735_: *mut leanh::LeanObject,
    mut v___y_7736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_7738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7743_: u8 = 0;
    let mut v___x_7744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_7745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_7747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_7748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_7749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_7751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_7752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_7753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7756_: u8 = 0;
    let mut v_tid_7757_: u64 = 0;
    let mut v_traces_7758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7761_: u8 = 0;
    let mut v___x_7762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7763_: f64 = 0.0;
    let mut v___x_7764_: u8 = 0;
    let mut v___x_7765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7783_: u8 = 0;
    let mut v_isSharedCheck_7784_: u8 = 0;
    let mut v_isSharedCheck_7785_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_7738_ = leanh::lean_ctor_get(v___y_7735_, 5);
                v___x_7739_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_7733_, v___y_7735_, v___y_7736_);
                v_a_7740_ = leanh::lean_ctor_get(v___x_7739_, 0);
                v_isSharedCheck_7785_ = (!leanh::lean_is_exclusive(v___x_7739_)) as u8;
                if v_isSharedCheck_7785_ == 0 {
                    v___x_7742_ = v___x_7739_;
                    v_isShared_7743_ = v_isSharedCheck_7785_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_7740_);
                    leanh::lean_dec(v___x_7739_);
                    v___x_7742_ = leanh::lean_box(0);
                    v_isShared_7743_ = v_isSharedCheck_7785_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7744_ = lean_st_ref_take(v___y_7736_);
                v_traceState_7745_ = leanh::lean_ctor_get(v___x_7744_, 4);
                v_env_7746_ = leanh::lean_ctor_get(v___x_7744_, 0);
                v_nextMacroScope_7747_ = leanh::lean_ctor_get(v___x_7744_, 1);
                v_ngen_7748_ = leanh::lean_ctor_get(v___x_7744_, 2);
                v_auxDeclNGen_7749_ = leanh::lean_ctor_get(v___x_7744_, 3);
                v_cache_7750_ = leanh::lean_ctor_get(v___x_7744_, 5);
                v_messages_7751_ = leanh::lean_ctor_get(v___x_7744_, 6);
                v_infoState_7752_ = leanh::lean_ctor_get(v___x_7744_, 7);
                v_snapshotTasks_7753_ = leanh::lean_ctor_get(v___x_7744_, 8);
                v_isSharedCheck_7784_ = (!leanh::lean_is_exclusive(v___x_7744_)) as u8;
                if v_isSharedCheck_7784_ == 0 {
                    v___x_7755_ = v___x_7744_;
                    v_isShared_7756_ = v_isSharedCheck_7784_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_7753_);
                    leanh::lean_inc(v_infoState_7752_);
                    leanh::lean_inc(v_messages_7751_);
                    leanh::lean_inc(v_cache_7750_);
                    leanh::lean_inc(v_traceState_7745_);
                    leanh::lean_inc(v_auxDeclNGen_7749_);
                    leanh::lean_inc(v_ngen_7748_);
                    leanh::lean_inc(v_nextMacroScope_7747_);
                    leanh::lean_inc(v_env_7746_);
                    leanh::lean_dec(v___x_7744_);
                    v___x_7755_ = leanh::lean_box(0);
                    v_isShared_7756_ = v_isSharedCheck_7784_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_7757_ = leanh::lean_ctor_get_uint64(
                    v_traceState_7745_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_7758_ = leanh::lean_ctor_get(v_traceState_7745_, 0);
                v_isSharedCheck_7783_ =
                    (!leanh::lean_is_exclusive(v_traceState_7745_)) as u8;
                if v_isSharedCheck_7783_ == 0 {
                    v___x_7760_ = v_traceState_7745_;
                    v_isShared_7761_ = v_isSharedCheck_7783_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_7758_);
                    leanh::lean_dec(v_traceState_7745_);
                    v___x_7760_ = leanh::lean_box(0);
                    v_isShared_7761_ = v_isSharedCheck_7783_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7762_ = leanh::lean_box(0);
                v___x_7763_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0);
                v___x_7764_ = 0;
                v___x_7765_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1;
                v___x_7766_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_7766_, 0, v_cls_7732_);
                leanh::lean_ctor_set(v___x_7766_, 1, v___x_7762_);
                leanh::lean_ctor_set(v___x_7766_, 2, v___x_7765_);
                leanh::lean_ctor_set_float(
                    v___x_7766_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_7763_,
                );
                leanh::lean_ctor_set_float(
                    v___x_7766_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_7763_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_7766_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_7764_,
                );
                v___x_7767_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2;
                v___x_7768_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_7768_, 0, v___x_7766_);
                leanh::lean_ctor_set(v___x_7768_, 1, v_a_7740_);
                leanh::lean_ctor_set(v___x_7768_, 2, v___x_7767_);
                leanh::lean_inc(v_ref_7738_);
                v___x_7769_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7769_, 0, v_ref_7738_);
                leanh::lean_ctor_set(v___x_7769_, 1, v___x_7768_);
                v___x_7770_ = l_Lean_PersistentArray_push___redArg(v_traces_7758_, v___x_7769_);
                if v_isShared_7761_ == 0 {
                    leanh::lean_ctor_set(v___x_7760_, 0, v___x_7770_);
                    v___x_7772_ = v___x_7760_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7782_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7782_, 0, v___x_7770_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_7782_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_7757_,
                    );
                    v___x_7772_ = v_reuseFailAlloc_7782_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_7756_ == 0 {
                    leanh::lean_ctor_set(v___x_7755_, 4, v___x_7772_);
                    v___x_7774_ = v___x_7755_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7781_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7781_, 0, v_env_7746_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7781_, 1, v_nextMacroScope_7747_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7781_, 2, v_ngen_7748_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7781_, 3, v_auxDeclNGen_7749_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7781_, 4, v___x_7772_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7781_, 5, v_cache_7750_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7781_, 6, v_messages_7751_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7781_, 7, v_infoState_7752_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7781_, 8, v_snapshotTasks_7753_);
                    v___x_7774_ = v_reuseFailAlloc_7781_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_7775_ = lean_st_ref_set(v___y_7736_, v___x_7774_);
                v___x_7776_ = leanh::lean_box(0);
                v___x_7777_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7777_, 0, v___x_7776_);
                leanh::lean_ctor_set(v___x_7777_, 1, v___y_7734_);
                if v_isShared_7743_ == 0 {
                    leanh::lean_ctor_set(v___x_7742_, 0, v___x_7777_);
                    v___x_7779_ = v___x_7742_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7780_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7780_, 0, v___x_7777_);
                    v___x_7779_ = v_reuseFailAlloc_7780_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7779_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___boxed(
    mut v_cls_7786_: *mut leanh::LeanObject,
    mut v_msg_7787_: *mut leanh::LeanObject,
    mut v___y_7788_: *mut leanh::LeanObject,
    mut v___y_7789_: *mut leanh::LeanObject,
    mut v___y_7790_: *mut leanh::LeanObject,
    mut v___y_7791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7792_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v_cls_7786_, v_msg_7787_, v___y_7788_, v___y_7789_, v___y_7790_);
    leanh::lean_dec(v___y_7790_);
    leanh::lean_dec_ref(v___y_7789_);
    return v_res_7792_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(
    mut v_a_7793_: *mut leanh::LeanObject,
    mut v_x_7794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_7796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7799_: u8 = 0;
    let mut v___x_7801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_7794_) == 0 {
                    v___x_7795_ = leanh::lean_box(0);
                    return v___x_7795_;
                } else {
                    v_key_7796_ = leanh::lean_ctor_get(v_x_7794_, 0);
                    v_value_7797_ = leanh::lean_ctor_get(v_x_7794_, 1);
                    v_tail_7798_ = leanh::lean_ctor_get(v_x_7794_, 2);
                    v___x_7799_ = l_Lean_instBEqFVarId_beq(v_key_7796_, v_a_7793_);
                    if v___x_7799_ == 0 {
                        v_x_7794_ = v_tail_7798_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_7797_);
                        v___x_7801_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_7801_, 0, v_value_7797_);
                        return v___x_7801_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg___boxed(
    mut v_a_7802_: *mut leanh::LeanObject,
    mut v_x_7803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7804_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7804_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_7802_, v_x_7803_);
    leanh::lean_dec(v_x_7803_);
    leanh::lean_dec(v_a_7802_);
    return v_res_7804_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(
    mut v_m_7805_: *mut leanh::LeanObject,
    mut v_a_7806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_7807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7809_: u64 = 0;
    let mut v___x_7810_: u64 = 0;
    let mut v___x_7811_: u64 = 0;
    let mut v_fold_7812_: u64 = 0;
    let mut v___x_7813_: u64 = 0;
    let mut v___x_7814_: u64 = 0;
    let mut v___x_7815_: u64 = 0;
    let mut v___x_7816_: usize = 0;
    let mut v___x_7817_: usize = 0;
    let mut v___x_7818_: usize = 0;
    let mut v___x_7819_: usize = 0;
    let mut v___x_7820_: usize = 0;
    let mut v___x_7821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_7807_ = leanh::lean_ctor_get(v_m_7805_, 1);
    v___x_7808_ = lean_array_get_size(v_buckets_7807_);
    v___x_7809_ = l_Lean_instHashableFVarId_hash(v_a_7806_);
    v___x_7810_ = 32u64;
    v___x_7811_ = lean_uint64_shift_right(v___x_7809_, v___x_7810_);
    v_fold_7812_ = lean_uint64_xor(v___x_7809_, v___x_7811_);
    v___x_7813_ = 16u64;
    v___x_7814_ = lean_uint64_shift_right(v_fold_7812_, v___x_7813_);
    v___x_7815_ = lean_uint64_xor(v_fold_7812_, v___x_7814_);
    v___x_7816_ = lean_uint64_to_usize(v___x_7815_);
    v___x_7817_ = lean_usize_of_nat(v___x_7808_);
    v___x_7818_ = 1usize;
    v___x_7819_ = lean_usize_sub(v___x_7817_, v___x_7818_);
    v___x_7820_ = lean_usize_land(v___x_7816_, v___x_7819_);
    v___x_7821_ = lean_array_uget_borrowed(v_buckets_7807_, v___x_7820_);
    v___x_7822_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_7806_, v___x_7821_);
    return v___x_7822_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg___boxed(
    mut v_m_7823_: *mut leanh::LeanObject,
    mut v_a_7824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7825_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_7823_, v_a_7824_);
    leanh::lean_dec(v_a_7824_);
    leanh::lean_dec_ref(v_m_7823_);
    return v_res_7825_;
}
pub unsafe fn l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0___boxed(
    mut v___x_7826_: *mut leanh::LeanObject,
    mut v_m_7827_: *mut leanh::LeanObject,
    mut v_e_7828_: *mut leanh::LeanObject,
    mut v___y_7829_: *mut leanh::LeanObject,
    mut v___y_7830_: *mut leanh::LeanObject,
    mut v___y_7831_: *mut leanh::LeanObject,
    mut v___y_7832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_19748__boxed_7833_: u8 = 0;
    let mut v_res_7834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_19748__boxed_7833_ = (leanh::lean_unbox(v___x_7826_) as u8);
    v_res_7834_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0(
        v___x_19748__boxed_7833_,
        v_m_7827_,
        v_e_7828_,
        v___y_7829_,
        v___y_7830_,
        v___y_7831_,
    );
    leanh::lean_dec(v___y_7831_);
    leanh::lean_dec_ref(v___y_7830_);
    leanh::lean_dec_ref(v_e_7828_);
    return v_res_7834_;
}
pub unsafe fn _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_7835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7835_ = leanh::lean_box(0);
    v___x_7836_ = leanh::lean_unsigned_to_nat(16);
    v___x_7837_ = lean_mk_array(v___x_7836_, v___x_7835_);
    return v___x_7837_;
}
pub unsafe fn _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_7838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7838_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0_once
        ),
        _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0,
    );
    v___x_7839_ = leanh::lean_unsigned_to_nat(0);
    v___x_7840_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7840_, 0, v___x_7839_);
    leanh::lean_ctor_set(v___x_7840_, 1, v___x_7838_);
    return v___x_7840_;
}
pub unsafe fn _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_7844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7844_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__4;
    v___x_7845_ = leanh::lean_unsigned_to_nat(4);
    v___x_7846_ = leanh::lean_unsigned_to_nat(384);
    v___x_7847_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3;
    v___x_7848_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2;
    v___x_7849_ = l_mkPanicMessageWithDecl(
        v___x_7848_,
        v___x_7847_,
        v___x_7846_,
        v___x_7845_,
        v___x_7844_,
    );
    return v___x_7849_;
}
pub unsafe fn _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_7851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7851_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__6;
    v___x_7852_ = l_Lean_stringToMessageData(v___x_7851_);
    return v___x_7852_;
}
pub unsafe fn _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_7861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7861_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10;
    v___x_7862_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__12;
    v___x_7863_ = l_Lean_Name_append(v___x_7862_, v___x_7861_);
    return v___x_7863_;
}
pub unsafe fn _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_7865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7865_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14;
    v___x_7866_ = l_Lean_stringToMessageData(v___x_7865_);
    return v___x_7866_;
}
pub unsafe fn _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_7868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7868_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__16;
    v___x_7869_ = l_Lean_stringToMessageData(v___x_7868_);
    return v___x_7869_;
}
pub unsafe fn l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(
    mut v_m_7870_: *mut leanh::LeanObject,
    mut v_fvarId_7871_: *mut leanh::LeanObject,
    mut v_a_7872_: *mut leanh::LeanObject,
    mut v_a_7873_: *mut leanh::LeanObject,
    mut v_a_7874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7880_: u8 = 0;
    let mut v_fst_7881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7885_: u8 = 0;
    let mut v_tempMark_7886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doneMark_7887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7889_: u8 = 0;
    let mut v_options_7890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_7891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_7892_: u8 = 0;
    let mut v___x_7893_: u8 = 0;
    let mut v___x_7894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tempMark_7900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doneMark_7901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newDecls_7902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newArgs_7903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7906_: u8 = 0;
    let mut v___x_7907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7918_: u8 = 0;
    let mut v_snd_7919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7922_: u8 = 0;
    let mut v___x_7923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tempMark_7924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doneMark_7925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newDecls_7926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newArgs_7927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7930_: u8 = 0;
    let mut v___x_7931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7943_: u8 = 0;
    let mut v_isSharedCheck_7944_: u8 = 0;
    let mut v_unused_7945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7946_: u8 = 0;
    let mut v_reuseFailAlloc_7947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7948_: u8 = 0;
    let mut v___y_7950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7953_: u8 = 0;
    let mut v___x_7954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tempMark_7958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7961_: u8 = 0;
    let mut v___x_7962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7968_: u8 = 0;
    let mut v___x_7969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tempMark_7981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7989_: u8 = 0;
    let mut v_isSharedCheck_7990_: u8 = 0;
    let mut v___x_7991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7876_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_7870_, v_fvarId_7871_);
                if leanh::lean_obj_tag(v___x_7876_) == 1 {
                    v_val_7877_ = leanh::lean_ctor_get(v___x_7876_, 0);
                    v_isSharedCheck_7990_ = (!leanh::lean_is_exclusive(v___x_7876_)) as u8;
                    if v_isSharedCheck_7990_ == 0 {
                        v___x_7879_ = v___x_7876_;
                        v_isShared_7880_ = v_isSharedCheck_7990_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_7877_);
                        leanh::lean_dec(v___x_7876_);
                        v___x_7879_ = leanh::lean_box(0);
                        v_isShared_7880_ = v_isSharedCheck_7990_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_7876_);
                    leanh::lean_dec_ref(v_m_7870_);
                    v___x_7991_ = leanh::lean_box(0);
                    v___x_7992_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7992_, 0, v___x_7991_);
                    leanh::lean_ctor_set(v___x_7992_, 1, v_a_7872_);
                    v___x_7993_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7993_, 0, v___x_7992_);
                    return v___x_7993_;
                }
            }
            1 => {
                v_fst_7881_ = leanh::lean_ctor_get(v_val_7877_, 0);
                v_snd_7882_ = leanh::lean_ctor_get(v_val_7877_, 1);
                v_isSharedCheck_7989_ = (!leanh::lean_is_exclusive(v_val_7877_)) as u8;
                if v_isSharedCheck_7989_ == 0 {
                    v___x_7884_ = v_val_7877_;
                    v_isShared_7885_ = v_isSharedCheck_7989_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_7882_);
                    leanh::lean_inc(v_fst_7881_);
                    leanh::lean_dec(v_val_7877_);
                    v___x_7884_ = leanh::lean_box(0);
                    v_isShared_7885_ = v_isSharedCheck_7989_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tempMark_7886_ = leanh::lean_ctor_get(v_a_7872_, 0);
                v_doneMark_7887_ = leanh::lean_ctor_get(v_a_7872_, 1);
                v___x_7888_ = l_Lean_LocalDecl_fvarId(v_fst_7881_);
                v___x_7889_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_doneMark_7887_, v___x_7888_);
                if v___x_7889_ == 0 {
                    leanh::lean_del_object(v___x_7884_);
                    leanh::lean_del_object(v___x_7879_);
                    v_options_7890_ = leanh::lean_ctor_get(v_a_7873_, 2);
                    v_inheritedTraceOptions_7891_ = leanh::lean_ctor_get(v_a_7873_, 13);
                    v_hasTrace_7892_ = leanh::lean_ctor_get_uint8(
                        v_options_7890_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    v___x_7893_ = 1;
                    v___x_7894_ = leanh::lean_box((v___x_7893_) as usize);
                    v___f_7895_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0___boxed as *mut core::ffi::c_void, 7, 2);
                    leanh::lean_closure_set(v___f_7895_, 0, v___x_7894_);
                    leanh::lean_closure_set(v___f_7895_, 1, v_m_7870_);
                    if v_hasTrace_7892_ == 0 {
                        leanh::lean_inc_ref(v_tempMark_7886_);
                        v___y_7957_ = v_a_7872_;
                        v_tempMark_7958_ = v_tempMark_7886_;
                        v___y_7959_ = v_a_7873_;
                        v___y_7960_ = v_a_7874_;
                        state = 13;
                        continue;
                    } else {
                        v___x_7966_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10;
                        v___x_7967_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once), _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
                        v___x_7968_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_7891_,
                            v_options_7890_,
                            v___x_7967_,
                        );
                        if v___x_7968_ == 0 {
                            leanh::lean_inc_ref(v_tempMark_7886_);
                            v___y_7957_ = v_a_7872_;
                            v_tempMark_7958_ = v_tempMark_7886_;
                            v___y_7959_ = v_a_7873_;
                            v___y_7960_ = v_a_7874_;
                            state = 13;
                            continue;
                        } else {
                            v___x_7969_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15_once), _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15);
                            leanh::lean_inc(v___x_7888_);
                            v___x_7970_ = l_Lean_mkFVar(v___x_7888_);
                            v___x_7971_ = l_Lean_MessageData_ofExpr(v___x_7970_);
                            v___x_7972_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_7972_, 0, v___x_7969_);
                            leanh::lean_ctor_set(v___x_7972_, 1, v___x_7971_);
                            v___x_7973_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17_once), _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17);
                            v___x_7974_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_7974_, 0, v___x_7972_);
                            leanh::lean_ctor_set(v___x_7974_, 1, v___x_7973_);
                            v___x_7975_ = l_Lean_LocalDecl_type(v_fst_7881_);
                            v___x_7976_ = l_Lean_MessageData_ofExpr(v___x_7975_);
                            v___x_7977_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_7977_, 0, v___x_7974_);
                            leanh::lean_ctor_set(v___x_7977_, 1, v___x_7976_);
                            v___x_7978_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v___x_7966_, v___x_7977_, v_a_7872_, v_a_7873_, v_a_7874_);
                            if leanh::lean_obj_tag(v___x_7978_) == 0 {
                                v_a_7979_ = leanh::lean_ctor_get(v___x_7978_, 0);
                                leanh::lean_inc(v_a_7979_);
                                leanh::lean_dec_ref_known(v___x_7978_, 1);
                                v_snd_7980_ = leanh::lean_ctor_get(v_a_7979_, 1);
                                leanh::lean_inc(v_snd_7980_);
                                leanh::lean_dec(v_a_7979_);
                                v_tempMark_7981_ = leanh::lean_ctor_get(v_snd_7980_, 0);
                                leanh::lean_inc_ref(v_tempMark_7981_);
                                v___y_7957_ = v_snd_7980_;
                                v_tempMark_7958_ = v_tempMark_7981_;
                                v___y_7959_ = v_a_7873_;
                                v___y_7960_ = v_a_7874_;
                                state = 13;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v___f_7895_);
                                leanh::lean_dec(v___x_7888_);
                                leanh::lean_dec(v_snd_7882_);
                                leanh::lean_dec(v_fst_7881_);
                                return v___x_7978_;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_7888_);
                    leanh::lean_dec(v_snd_7882_);
                    leanh::lean_dec(v_fst_7881_);
                    leanh::lean_dec_ref(v_m_7870_);
                    v___x_7982_ = leanh::lean_box(0);
                    if v_isShared_7885_ == 0 {
                        leanh::lean_ctor_set(v___x_7884_, 1, v_a_7872_);
                        leanh::lean_ctor_set(v___x_7884_, 0, v___x_7982_);
                        v___x_7984_ = v___x_7884_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_7988_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7988_, 0, v___x_7982_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7988_, 1, v_a_7872_);
                        v___x_7984_ = v_reuseFailAlloc_7988_;
                        state = 14;
                        continue;
                    }
                }
            }
            3 => {
                v_tempMark_7900_ = leanh::lean_ctor_get(v___y_7897_, 0);
                v_doneMark_7901_ = leanh::lean_ctor_get(v___y_7897_, 1);
                v_newDecls_7902_ = leanh::lean_ctor_get(v___y_7897_, 2);
                v_newArgs_7903_ = leanh::lean_ctor_get(v___y_7897_, 3);
                v_isSharedCheck_7948_ = (!leanh::lean_is_exclusive(v___y_7897_)) as u8;
                if v_isSharedCheck_7948_ == 0 {
                    v___x_7905_ = v___y_7897_;
                    v_isShared_7906_ = v_isSharedCheck_7948_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_newArgs_7903_);
                    leanh::lean_inc(v_newDecls_7902_);
                    leanh::lean_inc(v_doneMark_7901_);
                    leanh::lean_inc(v_tempMark_7900_);
                    leanh::lean_dec(v___y_7897_);
                    v___x_7905_ = leanh::lean_box(0);
                    v_isShared_7906_ = v_isSharedCheck_7948_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7907_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1_once), _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1);
                v___x_7908_ = lean_st_mk_ref(v___x_7907_);
                v___x_7909_ = leanh::lean_box(0);
                leanh::lean_inc(v___x_7888_);
                v___x_7910_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_tempMark_7900_, v___x_7888_, v___x_7909_);
                if v_isShared_7906_ == 0 {
                    leanh::lean_ctor_set(v___x_7905_, 0, v___x_7910_);
                    v___x_7912_ = v___x_7905_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7947_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7947_, 0, v___x_7910_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7947_, 1, v_doneMark_7901_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7947_, 2, v_newDecls_7902_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7947_, 3, v_newArgs_7903_);
                    v___x_7912_ = v_reuseFailAlloc_7947_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_7913_ = l_Lean_LocalDecl_type(v_fst_7881_);
                v___x_7914_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v___f_7895_, v___x_7913_, v___x_7908_, v___x_7912_, v___y_7898_, v___y_7899_);
                if leanh::lean_obj_tag(v___x_7914_) == 0 {
                    v_a_7915_ = leanh::lean_ctor_get(v___x_7914_, 0);
                    v_isSharedCheck_7946_ = (!leanh::lean_is_exclusive(v___x_7914_)) as u8;
                    if v_isSharedCheck_7946_ == 0 {
                        v___x_7917_ = v___x_7914_;
                        v_isShared_7918_ = v_isSharedCheck_7946_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7915_);
                        leanh::lean_dec(v___x_7914_);
                        v___x_7917_ = leanh::lean_box(0);
                        v_isShared_7918_ = v_isSharedCheck_7946_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_7908_);
                    leanh::lean_dec(v___x_7888_);
                    leanh::lean_dec(v_snd_7882_);
                    leanh::lean_dec(v_fst_7881_);
                    return v___x_7914_;
                }
            }
            6 => {
                v_snd_7919_ = leanh::lean_ctor_get(v_a_7915_, 1);
                v_isSharedCheck_7944_ = (!leanh::lean_is_exclusive(v_a_7915_)) as u8;
                if v_isSharedCheck_7944_ == 0 {
                    v_unused_7945_ = leanh::lean_ctor_get(v_a_7915_, 0);
                    leanh::lean_dec(v_unused_7945_);
                    v___x_7921_ = v_a_7915_;
                    v_isShared_7922_ = v_isSharedCheck_7944_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_7919_);
                    leanh::lean_dec(v_a_7915_);
                    v___x_7921_ = leanh::lean_box(0);
                    v_isShared_7922_ = v_isSharedCheck_7944_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_7923_ = lean_st_ref_get(v___x_7908_);
                leanh::lean_dec(v___x_7908_);
                leanh::lean_dec(v___x_7923_);
                v_tempMark_7924_ = leanh::lean_ctor_get(v_snd_7919_, 0);
                v_doneMark_7925_ = leanh::lean_ctor_get(v_snd_7919_, 1);
                v_newDecls_7926_ = leanh::lean_ctor_get(v_snd_7919_, 2);
                v_newArgs_7927_ = leanh::lean_ctor_get(v_snd_7919_, 3);
                v_isSharedCheck_7943_ = (!leanh::lean_is_exclusive(v_snd_7919_)) as u8;
                if v_isSharedCheck_7943_ == 0 {
                    v___x_7929_ = v_snd_7919_;
                    v_isShared_7930_ = v_isSharedCheck_7943_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_newArgs_7927_);
                    leanh::lean_inc(v_newDecls_7926_);
                    leanh::lean_inc(v_doneMark_7925_);
                    leanh::lean_inc(v_tempMark_7924_);
                    leanh::lean_dec(v_snd_7919_);
                    v___x_7929_ = leanh::lean_box(0);
                    v_isShared_7930_ = v_isSharedCheck_7943_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_7931_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_doneMark_7925_, v___x_7888_, v___x_7909_);
                v___x_7932_ = lean_array_push(v_newDecls_7926_, v_fst_7881_);
                v___x_7933_ = lean_array_push(v_newArgs_7927_, v_snd_7882_);
                if v_isShared_7930_ == 0 {
                    leanh::lean_ctor_set(v___x_7929_, 3, v___x_7933_);
                    leanh::lean_ctor_set(v___x_7929_, 2, v___x_7932_);
                    leanh::lean_ctor_set(v___x_7929_, 1, v___x_7931_);
                    v___x_7935_ = v___x_7929_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7942_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7942_, 0, v_tempMark_7924_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7942_, 1, v___x_7931_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7942_, 2, v___x_7932_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7942_, 3, v___x_7933_);
                    v___x_7935_ = v_reuseFailAlloc_7942_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_7922_ == 0 {
                    leanh::lean_ctor_set(v___x_7921_, 1, v___x_7935_);
                    leanh::lean_ctor_set(v___x_7921_, 0, v___x_7909_);
                    v___x_7937_ = v___x_7921_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7941_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7941_, 0, v___x_7909_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7941_, 1, v___x_7935_);
                    v___x_7937_ = v_reuseFailAlloc_7941_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_7918_ == 0 {
                    leanh::lean_ctor_set(v___x_7917_, 0, v___x_7937_);
                    v___x_7939_ = v___x_7917_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7940_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7940_, 0, v___x_7937_);
                    v___x_7939_ = v_reuseFailAlloc_7940_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_7939_;
            }
            12 => {
                v___x_7953_ = l_Lean_LocalDecl_isLet(v_fst_7881_, v___x_7893_);
                if v___x_7953_ == 0 {
                    v___y_7897_ = v___y_7950_;
                    v___y_7898_ = v___y_7951_;
                    v___y_7899_ = v___y_7952_;
                    state = 3;
                    continue;
                } else {
                    if v___x_7889_ == 0 {
                        leanh::lean_dec_ref(v___f_7895_);
                        leanh::lean_dec(v___x_7888_);
                        leanh::lean_dec(v_snd_7882_);
                        leanh::lean_dec(v_fst_7881_);
                        v___x_7954_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5_once), _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5);
                        v___x_7955_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v___x_7954_, v___y_7950_, v___y_7951_, v___y_7952_);
                        return v___x_7955_;
                    } else {
                        v___y_7897_ = v___y_7950_;
                        v___y_7898_ = v___y_7951_;
                        v___y_7899_ = v___y_7952_;
                        state = 3;
                        continue;
                    }
                }
            }
            13 => {
                v___x_7961_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_tempMark_7958_, v___x_7888_);
                leanh::lean_dec_ref(v_tempMark_7958_);
                if v___x_7961_ == 0 {
                    v___y_7950_ = v___y_7957_;
                    v___y_7951_ = v___y_7959_;
                    v___y_7952_ = v___y_7960_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_7957_);
                    v___x_7962_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7_once), _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7);
                    v___x_7963_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v___x_7962_, v___y_7959_, v___y_7960_);
                    if leanh::lean_obj_tag(v___x_7963_) == 0 {
                        v_a_7964_ = leanh::lean_ctor_get(v___x_7963_, 0);
                        leanh::lean_inc(v_a_7964_);
                        leanh::lean_dec_ref_known(v___x_7963_, 1);
                        v_snd_7965_ = leanh::lean_ctor_get(v_a_7964_, 1);
                        leanh::lean_inc(v_snd_7965_);
                        leanh::lean_dec(v_a_7964_);
                        v___y_7950_ = v_snd_7965_;
                        v___y_7951_ = v___y_7959_;
                        v___y_7952_ = v___y_7960_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___f_7895_);
                        leanh::lean_dec(v___x_7888_);
                        leanh::lean_dec(v_snd_7882_);
                        leanh::lean_dec(v_fst_7881_);
                        return v___x_7963_;
                    }
                }
            }
            14 => {
                if v_isShared_7880_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_7879_, 0);
                    leanh::lean_ctor_set(v___x_7879_, 0, v___x_7984_);
                    v___x_7986_ = v___x_7879_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_7987_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7987_, 0, v___x_7984_);
                    v___x_7986_ = v_reuseFailAlloc_7987_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_7986_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0(
    mut v___x_7994_: u8,
    mut v_m_7995_: *mut leanh::LeanObject,
    mut v_e_7996_: *mut leanh::LeanObject,
    mut v___y_7997_: *mut leanh::LeanObject,
    mut v___y_7998_: *mut leanh::LeanObject,
    mut v___y_7999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_8002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8006_: u8 = 0;
    let mut v___x_8007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8010_: u8 = 0;
    let mut v___x_8011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8018_: u8 = 0;
    let mut v___x_8020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8022_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8006_ = l_Lean_Expr_hasFVar(v_e_7996_);
                if v___x_8006_ == 0 {
                    leanh::lean_dec_ref(v_m_7995_);
                    v___x_8007_ = leanh::lean_box((v___x_8006_) as usize);
                    v___x_8008_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_8008_, 0, v___x_8007_);
                    leanh::lean_ctor_set(v___x_8008_, 1, v___y_7997_);
                    v___x_8009_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8009_, 0, v___x_8008_);
                    return v___x_8009_;
                } else {
                    v___x_8010_ = l_Lean_Expr_isFVar(v_e_7996_);
                    if v___x_8010_ == 0 {
                        leanh::lean_dec_ref(v_m_7995_);
                        v___y_8002_ = v___y_7997_;
                        state = 1;
                        continue;
                    } else {
                        v___x_8011_ = l_Lean_Expr_fvarId_x21(v_e_7996_);
                        v___x_8012_ =
                            l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(
                                v_m_7995_,
                                v___x_8011_,
                                v___y_7997_,
                                v___y_7998_,
                                v___y_7999_,
                            );
                        leanh::lean_dec(v___x_8011_);
                        if leanh::lean_obj_tag(v___x_8012_) == 0 {
                            v_a_8013_ = leanh::lean_ctor_get(v___x_8012_, 0);
                            leanh::lean_inc(v_a_8013_);
                            leanh::lean_dec_ref_known(v___x_8012_, 1);
                            v_snd_8014_ = leanh::lean_ctor_get(v_a_8013_, 1);
                            leanh::lean_inc(v_snd_8014_);
                            leanh::lean_dec(v_a_8013_);
                            v___y_8002_ = v_snd_8014_;
                            state = 1;
                            continue;
                        } else {
                            v_a_8015_ = leanh::lean_ctor_get(v___x_8012_, 0);
                            v_isSharedCheck_8022_ =
                                (!leanh::lean_is_exclusive(v___x_8012_)) as u8;
                            if v_isSharedCheck_8022_ == 0 {
                                v___x_8017_ = v___x_8012_;
                                v_isShared_8018_ = v_isSharedCheck_8022_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_8015_);
                                leanh::lean_dec(v___x_8012_);
                                v___x_8017_ = leanh::lean_box(0);
                                v_isShared_8018_ = v_isSharedCheck_8022_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_8003_ = leanh::lean_box((v___x_7994_) as usize);
                v___x_8004_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8004_, 0, v___x_8003_);
                leanh::lean_ctor_set(v___x_8004_, 1, v___y_8002_);
                v___x_8005_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_8005_, 0, v___x_8004_);
                return v___x_8005_;
            }
            2 => {
                if v_isShared_8018_ == 0 {
                    v___x_8020_ = v___x_8017_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8021_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8021_, 0, v_a_8015_);
                    v___x_8020_ = v_reuseFailAlloc_8021_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_8020_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___boxed(
    mut v_m_8023_: *mut leanh::LeanObject,
    mut v_fvarId_8024_: *mut leanh::LeanObject,
    mut v_a_8025_: *mut leanh::LeanObject,
    mut v_a_8026_: *mut leanh::LeanObject,
    mut v_a_8027_: *mut leanh::LeanObject,
    mut v_a_8028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8029_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(
        v_m_8023_,
        v_fvarId_8024_,
        v_a_8025_,
        v_a_8026_,
        v_a_8027_,
    );
    leanh::lean_dec(v_a_8027_);
    leanh::lean_dec_ref(v_a_8026_);
    leanh::lean_dec(v_fvarId_8024_);
    return v_res_8029_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0(
    mut v_00_u03b2_8030_: *mut leanh::LeanObject,
    mut v_m_8031_: *mut leanh::LeanObject,
    mut v_a_8032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8033_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8033_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_8031_, v_a_8032_);
    return v___x_8033_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___boxed(
    mut v_00_u03b2_8034_: *mut leanh::LeanObject,
    mut v_m_8035_: *mut leanh::LeanObject,
    mut v_a_8036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8037_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0(v_00_u03b2_8034_, v_m_8035_, v_a_8036_);
    leanh::lean_dec(v_a_8036_);
    leanh::lean_dec_ref(v_m_8035_);
    return v_res_8037_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1(
    mut v_00_u03b2_8038_: *mut leanh::LeanObject,
    mut v_m_8039_: *mut leanh::LeanObject,
    mut v_a_8040_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_8041_: u8 = 0;
    v___x_8041_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_m_8039_, v_a_8040_);
    return v___x_8041_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___boxed(
    mut v_00_u03b2_8042_: *mut leanh::LeanObject,
    mut v_m_8043_: *mut leanh::LeanObject,
    mut v_a_8044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8045_: u8 = 0;
    let mut v_r_8046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8045_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1(v_00_u03b2_8042_, v_m_8043_, v_a_8044_);
    leanh::lean_dec(v_a_8044_);
    leanh::lean_dec_ref(v_m_8043_);
    v_r_8046_ = leanh::lean_box((v_res_8045_) as usize);
    return v_r_8046_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(
    mut v_00_u03b2_8047_: *mut leanh::LeanObject,
    mut v_m_8048_: *mut leanh::LeanObject,
    mut v_a_8049_: *mut leanh::LeanObject,
    mut v_b_8050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8051_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_m_8048_, v_a_8049_, v_b_8050_);
    return v___x_8051_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(
    mut v_00_u03b1_8052_: *mut leanh::LeanObject,
    mut v_msg_8053_: *mut leanh::LeanObject,
    mut v___y_8054_: *mut leanh::LeanObject,
    mut v___y_8055_: *mut leanh::LeanObject,
    mut v___y_8056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8058_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v_msg_8053_, v___y_8055_, v___y_8056_);
    return v___x_8058_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___boxed(
    mut v_00_u03b1_8059_: *mut leanh::LeanObject,
    mut v_msg_8060_: *mut leanh::LeanObject,
    mut v___y_8061_: *mut leanh::LeanObject,
    mut v___y_8062_: *mut leanh::LeanObject,
    mut v___y_8063_: *mut leanh::LeanObject,
    mut v___y_8064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8065_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(v_00_u03b1_8059_, v_msg_8060_, v___y_8061_, v___y_8062_, v___y_8063_);
    leanh::lean_dec(v___y_8063_);
    leanh::lean_dec_ref(v___y_8062_);
    leanh::lean_dec_ref(v___y_8061_);
    return v_res_8065_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0(
    mut v_00_u03b2_8066_: *mut leanh::LeanObject,
    mut v_a_8067_: *mut leanh::LeanObject,
    mut v_x_8068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8069_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_8067_, v_x_8068_);
    return v___x_8069_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___boxed(
    mut v_00_u03b2_8070_: *mut leanh::LeanObject,
    mut v_a_8071_: *mut leanh::LeanObject,
    mut v_x_8072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8073_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0(v_00_u03b2_8070_, v_a_8071_, v_x_8072_);
    leanh::lean_dec(v_x_8072_);
    leanh::lean_dec(v_a_8071_);
    return v_res_8073_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2(
    mut v_00_u03b2_8074_: *mut leanh::LeanObject,
    mut v_a_8075_: *mut leanh::LeanObject,
    mut v_x_8076_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_8077_: u8 = 0;
    v___x_8077_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_8075_, v_x_8076_);
    return v___x_8077_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___boxed(
    mut v_00_u03b2_8078_: *mut leanh::LeanObject,
    mut v_a_8079_: *mut leanh::LeanObject,
    mut v_x_8080_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8081_: u8 = 0;
    let mut v_r_8082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8081_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2(v_00_u03b2_8078_, v_a_8079_, v_x_8080_);
    leanh::lean_dec(v_x_8080_);
    leanh::lean_dec(v_a_8079_);
    v_r_8082_ = leanh::lean_box((v_res_8081_) as usize);
    return v_r_8082_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4(
    mut v_00_u03b2_8083_: *mut leanh::LeanObject,
    mut v_data_8084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8085_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_data_8084_);
    return v___x_8085_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6(
    mut v_00_u03b2_8086_: *mut leanh::LeanObject,
    mut v_m_8087_: *mut leanh::LeanObject,
    mut v_a_8088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8089_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v_m_8087_, v_a_8088_);
    return v___x_8089_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___boxed(
    mut v_00_u03b2_8090_: *mut leanh::LeanObject,
    mut v_m_8091_: *mut leanh::LeanObject,
    mut v_a_8092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8093_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6(v_00_u03b2_8090_, v_m_8091_, v_a_8092_);
    leanh::lean_dec_ref(v_a_8092_);
    leanh::lean_dec_ref(v_m_8091_);
    return v_res_8093_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7(
    mut v_00_u03b2_8094_: *mut leanh::LeanObject,
    mut v_m_8095_: *mut leanh::LeanObject,
    mut v_a_8096_: *mut leanh::LeanObject,
    mut v_b_8097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8098_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(v_m_8095_, v_a_8096_, v_b_8097_);
    return v___x_8098_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6(
    mut v_00_u03b2_8099_: *mut leanh::LeanObject,
    mut v_i_8100_: *mut leanh::LeanObject,
    mut v_source_8101_: *mut leanh::LeanObject,
    mut v_target_8102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8103_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(v_i_8100_, v_source_8101_, v_target_8102_);
    return v___x_8103_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9(
    mut v_00_u03b2_8104_: *mut leanh::LeanObject,
    mut v_a_8105_: *mut leanh::LeanObject,
    mut v_x_8106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8107_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_8105_, v_x_8106_);
    return v___x_8107_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___boxed(
    mut v_00_u03b2_8108_: *mut leanh::LeanObject,
    mut v_a_8109_: *mut leanh::LeanObject,
    mut v_x_8110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8111_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9(v_00_u03b2_8108_, v_a_8109_, v_x_8110_);
    leanh::lean_dec(v_x_8110_);
    leanh::lean_dec_ref(v_a_8109_);
    return v_res_8111_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11(
    mut v_00_u03b2_8112_: *mut leanh::LeanObject,
    mut v_a_8113_: *mut leanh::LeanObject,
    mut v_x_8114_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_8115_: u8 = 0;
    v___x_8115_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_8113_, v_x_8114_);
    return v___x_8115_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___boxed(
    mut v_00_u03b2_8116_: *mut leanh::LeanObject,
    mut v_a_8117_: *mut leanh::LeanObject,
    mut v_x_8118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8119_: u8 = 0;
    let mut v_r_8120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8119_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11(v_00_u03b2_8116_, v_a_8117_, v_x_8118_);
    leanh::lean_dec(v_x_8118_);
    leanh::lean_dec_ref(v_a_8117_);
    v_r_8120_ = leanh::lean_box((v_res_8119_) as usize);
    return v_r_8120_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12(
    mut v_00_u03b2_8121_: *mut leanh::LeanObject,
    mut v_data_8122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8123_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(v_data_8122_);
    return v___x_8123_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13(
    mut v_00_u03b2_8124_: *mut leanh::LeanObject,
    mut v_a_8125_: *mut leanh::LeanObject,
    mut v_b_8126_: *mut leanh::LeanObject,
    mut v_x_8127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8128_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_8125_, v_b_8126_, v_x_8127_);
    return v___x_8128_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11(
    mut v_00_u03b2_8129_: *mut leanh::LeanObject,
    mut v_x_8130_: *mut leanh::LeanObject,
    mut v_x_8131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8132_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(v_x_8130_, v_x_8131_);
    return v___x_8132_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17(
    mut v_00_u03b2_8133_: *mut leanh::LeanObject,
    mut v_i_8134_: *mut leanh::LeanObject,
    mut v_source_8135_: *mut leanh::LeanObject,
    mut v_target_8136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8137_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(v_i_8134_, v_source_8135_, v_target_8136_);
    return v___x_8137_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18(
    mut v_00_u03b2_8138_: *mut leanh::LeanObject,
    mut v_x_8139_: *mut leanh::LeanObject,
    mut v_x_8140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8141_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(v_x_8139_, v_x_8140_);
    return v___x_8141_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(
    mut v_msg_8143_: *mut leanh::LeanObject,
    mut v___y_8144_: *mut leanh::LeanObject,
    mut v___y_8145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_8147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8561__overap_8148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_8147_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___closed__0;
    v___x_8561__overap_8148_ = lean_panic_fn_borrowed(v___f_8147_, v_msg_8143_);
    leanh::lean_inc(v___y_8145_);
    leanh::lean_inc_ref(v___y_8144_);
    v___x_8149_ = leanh::lean_apply_3(
        v___x_8561__overap_8148_,
        v___y_8144_,
        v___y_8145_,
        leanh::lean_box(0),
    );
    return v___x_8149_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___boxed(
    mut v_msg_8150_: *mut leanh::LeanObject,
    mut v___y_8151_: *mut leanh::LeanObject,
    mut v___y_8152_: *mut leanh::LeanObject,
    mut v___y_8153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8154_ =
        l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(
            v_msg_8150_,
            v___y_8151_,
            v___y_8152_,
        );
    leanh::lean_dec(v___y_8152_);
    leanh::lean_dec_ref(v___y_8151_);
    return v_res_8154_;
}
pub unsafe fn l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(
    mut v_newDecls_8155_: *mut leanh::LeanObject,
    mut v_newArgs_8156_: *mut leanh::LeanObject,
    mut v_____r_8157_: *mut leanh::LeanObject,
    mut v___y_8158_: *mut leanh::LeanObject,
    mut v___y_8159_: *mut leanh::LeanObject,
    mut v___y_8160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8162_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_8162_, 0, v_newDecls_8155_);
    leanh::lean_ctor_set(v___x_8162_, 1, v_newArgs_8156_);
    v___x_8163_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_8163_, 0, v___x_8162_);
    leanh::lean_ctor_set(v___x_8163_, 1, v___y_8158_);
    v___x_8164_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_8164_, 0, v___x_8163_);
    return v___x_8164_;
}
pub unsafe fn l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0___boxed(
    mut v_newDecls_8165_: *mut leanh::LeanObject,
    mut v_newArgs_8166_: *mut leanh::LeanObject,
    mut v_____r_8167_: *mut leanh::LeanObject,
    mut v___y_8168_: *mut leanh::LeanObject,
    mut v___y_8169_: *mut leanh::LeanObject,
    mut v___y_8170_: *mut leanh::LeanObject,
    mut v___y_8171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8172_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(
        v_newDecls_8165_,
        v_newArgs_8166_,
        v_____r_8167_,
        v___y_8168_,
        v___y_8169_,
        v___y_8170_,
    );
    leanh::lean_dec(v___y_8170_);
    leanh::lean_dec_ref(v___y_8169_);
    return v_res_8172_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(
    mut v_cls_8173_: *mut leanh::LeanObject,
    mut v_msg_8174_: *mut leanh::LeanObject,
    mut v___y_8175_: *mut leanh::LeanObject,
    mut v___y_8176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_8178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8183_: u8 = 0;
    let mut v___x_8184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_8185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_8186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_8187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_8188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_8189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_8190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_8191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_8192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_8193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8196_: u8 = 0;
    let mut v_tid_8197_: u64 = 0;
    let mut v_traces_8198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8201_: u8 = 0;
    let mut v___x_8202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8203_: f64 = 0.0;
    let mut v___x_8204_: u8 = 0;
    let mut v___x_8205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8222_: u8 = 0;
    let mut v_isSharedCheck_8223_: u8 = 0;
    let mut v_isSharedCheck_8224_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_8178_ = leanh::lean_ctor_get(v___y_8175_, 5);
                v___x_8179_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_8174_, v___y_8175_, v___y_8176_);
                v_a_8180_ = leanh::lean_ctor_get(v___x_8179_, 0);
                v_isSharedCheck_8224_ = (!leanh::lean_is_exclusive(v___x_8179_)) as u8;
                if v_isSharedCheck_8224_ == 0 {
                    v___x_8182_ = v___x_8179_;
                    v_isShared_8183_ = v_isSharedCheck_8224_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_8180_);
                    leanh::lean_dec(v___x_8179_);
                    v___x_8182_ = leanh::lean_box(0);
                    v_isShared_8183_ = v_isSharedCheck_8224_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8184_ = lean_st_ref_take(v___y_8176_);
                v_traceState_8185_ = leanh::lean_ctor_get(v___x_8184_, 4);
                v_env_8186_ = leanh::lean_ctor_get(v___x_8184_, 0);
                v_nextMacroScope_8187_ = leanh::lean_ctor_get(v___x_8184_, 1);
                v_ngen_8188_ = leanh::lean_ctor_get(v___x_8184_, 2);
                v_auxDeclNGen_8189_ = leanh::lean_ctor_get(v___x_8184_, 3);
                v_cache_8190_ = leanh::lean_ctor_get(v___x_8184_, 5);
                v_messages_8191_ = leanh::lean_ctor_get(v___x_8184_, 6);
                v_infoState_8192_ = leanh::lean_ctor_get(v___x_8184_, 7);
                v_snapshotTasks_8193_ = leanh::lean_ctor_get(v___x_8184_, 8);
                v_isSharedCheck_8223_ = (!leanh::lean_is_exclusive(v___x_8184_)) as u8;
                if v_isSharedCheck_8223_ == 0 {
                    v___x_8195_ = v___x_8184_;
                    v_isShared_8196_ = v_isSharedCheck_8223_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_8193_);
                    leanh::lean_inc(v_infoState_8192_);
                    leanh::lean_inc(v_messages_8191_);
                    leanh::lean_inc(v_cache_8190_);
                    leanh::lean_inc(v_traceState_8185_);
                    leanh::lean_inc(v_auxDeclNGen_8189_);
                    leanh::lean_inc(v_ngen_8188_);
                    leanh::lean_inc(v_nextMacroScope_8187_);
                    leanh::lean_inc(v_env_8186_);
                    leanh::lean_dec(v___x_8184_);
                    v___x_8195_ = leanh::lean_box(0);
                    v_isShared_8196_ = v_isSharedCheck_8223_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_8197_ = leanh::lean_ctor_get_uint64(
                    v_traceState_8185_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_8198_ = leanh::lean_ctor_get(v_traceState_8185_, 0);
                v_isSharedCheck_8222_ =
                    (!leanh::lean_is_exclusive(v_traceState_8185_)) as u8;
                if v_isSharedCheck_8222_ == 0 {
                    v___x_8200_ = v_traceState_8185_;
                    v_isShared_8201_ = v_isSharedCheck_8222_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_8198_);
                    leanh::lean_dec(v_traceState_8185_);
                    v___x_8200_ = leanh::lean_box(0);
                    v_isShared_8201_ = v_isSharedCheck_8222_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_8202_ = leanh::lean_box(0);
                v___x_8203_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0);
                v___x_8204_ = 0;
                v___x_8205_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1;
                v___x_8206_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_8206_, 0, v_cls_8173_);
                leanh::lean_ctor_set(v___x_8206_, 1, v___x_8202_);
                leanh::lean_ctor_set(v___x_8206_, 2, v___x_8205_);
                leanh::lean_ctor_set_float(
                    v___x_8206_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_8203_,
                );
                leanh::lean_ctor_set_float(
                    v___x_8206_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_8203_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_8206_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_8204_,
                );
                v___x_8207_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2;
                v___x_8208_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_8208_, 0, v___x_8206_);
                leanh::lean_ctor_set(v___x_8208_, 1, v_a_8180_);
                leanh::lean_ctor_set(v___x_8208_, 2, v___x_8207_);
                leanh::lean_inc(v_ref_8178_);
                v___x_8209_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8209_, 0, v_ref_8178_);
                leanh::lean_ctor_set(v___x_8209_, 1, v___x_8208_);
                v___x_8210_ = l_Lean_PersistentArray_push___redArg(v_traces_8198_, v___x_8209_);
                if v_isShared_8201_ == 0 {
                    leanh::lean_ctor_set(v___x_8200_, 0, v___x_8210_);
                    v___x_8212_ = v___x_8200_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8221_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8221_, 0, v___x_8210_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_8221_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_8197_,
                    );
                    v___x_8212_ = v_reuseFailAlloc_8221_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_8196_ == 0 {
                    leanh::lean_ctor_set(v___x_8195_, 4, v___x_8212_);
                    v___x_8214_ = v___x_8195_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8220_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8220_, 0, v_env_8186_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8220_, 1, v_nextMacroScope_8187_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8220_, 2, v_ngen_8188_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8220_, 3, v_auxDeclNGen_8189_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8220_, 4, v___x_8212_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8220_, 5, v_cache_8190_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8220_, 6, v_messages_8191_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8220_, 7, v_infoState_8192_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8220_, 8, v_snapshotTasks_8193_);
                    v___x_8214_ = v_reuseFailAlloc_8220_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_8215_ = lean_st_ref_set(v___y_8176_, v___x_8214_);
                v___x_8216_ = leanh::lean_box(0);
                if v_isShared_8183_ == 0 {
                    leanh::lean_ctor_set(v___x_8182_, 0, v___x_8216_);
                    v___x_8218_ = v___x_8182_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8219_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8219_, 0, v___x_8216_);
                    v___x_8218_ = v_reuseFailAlloc_8219_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8218_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6___boxed(
    mut v_cls_8225_: *mut leanh::LeanObject,
    mut v_msg_8226_: *mut leanh::LeanObject,
    mut v___y_8227_: *mut leanh::LeanObject,
    mut v___y_8228_: *mut leanh::LeanObject,
    mut v___y_8229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8230_ =
        l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(
            v_cls_8225_,
            v_msg_8226_,
            v___y_8227_,
            v___y_8228_,
        );
    leanh::lean_dec(v___y_8228_);
    leanh::lean_dec_ref(v___y_8227_);
    return v_res_8230_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(
    mut v_sz_8231_: usize,
    mut v_i_8232_: usize,
    mut v_bs_8233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8234_: u8 = 0;
    let mut v_v_8235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_8237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8240_: usize = 0;
    let mut v___x_8241_: usize = 0;
    let mut v___x_8242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8234_ = lean_usize_dec_lt(v_i_8232_, v_sz_8231_);
                if v___x_8234_ == 0 {
                    return v_bs_8233_;
                } else {
                    v_v_8235_ = lean_array_uget(v_bs_8233_, v_i_8232_);
                    v___x_8236_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_8237_ = lean_array_uset(v_bs_8233_, v_i_8232_, v___x_8236_);
                    v___x_8238_ = l_Lean_LocalDecl_fvarId(v_v_8235_);
                    leanh::lean_dec(v_v_8235_);
                    v___x_8239_ = l_Lean_mkFVar(v___x_8238_);
                    v___x_8240_ = 1usize;
                    v___x_8241_ = lean_usize_add(v_i_8232_, v___x_8240_);
                    v___x_8242_ = lean_array_uset(v_bs_x27_8237_, v_i_8232_, v___x_8239_);
                    v_i_8232_ = v___x_8241_;
                    v_bs_8233_ = v___x_8242_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4___boxed(
    mut v_sz_8244_: *mut leanh::LeanObject,
    mut v_i_8245_: *mut leanh::LeanObject,
    mut v_bs_8246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_8247_: usize = 0;
    let mut v_i_boxed_8248_: usize = 0;
    let mut v_res_8249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_8247_ = leanh::lean_unbox_usize(v_sz_8244_);
    leanh::lean_dec(v_sz_8244_);
    v_i_boxed_8248_ = leanh::lean_unbox_usize(v_i_8245_);
    leanh::lean_dec(v_i_8245_);
    v_res_8249_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(v_sz_boxed_8247_, v_i_boxed_8248_, v_bs_8246_);
    return v_res_8249_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(
    mut v___x_8250_: *mut leanh::LeanObject,
    mut v_as_8251_: *mut leanh::LeanObject,
    mut v_sz_8252_: usize,
    mut v_i_8253_: usize,
    mut v_b_8254_: *mut leanh::LeanObject,
    mut v___y_8255_: *mut leanh::LeanObject,
    mut v___y_8256_: *mut leanh::LeanObject,
    mut v___y_8257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8259_: u8 = 0;
    let mut v___x_8260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8268_: usize = 0;
    let mut v___x_8269_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8259_ = lean_usize_dec_lt(v_i_8253_, v_sz_8252_);
                if v___x_8259_ == 0 {
                    leanh::lean_dec_ref(v___x_8250_);
                    v___x_8260_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_8260_, 0, v_b_8254_);
                    leanh::lean_ctor_set(v___x_8260_, 1, v___y_8255_);
                    v___x_8261_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8261_, 0, v___x_8260_);
                    return v___x_8261_;
                } else {
                    v_a_8262_ = lean_array_uget_borrowed(v_as_8251_, v_i_8253_);
                    v___x_8263_ = l_Lean_LocalDecl_fvarId(v_a_8262_);
                    leanh::lean_inc_ref(v___x_8250_);
                    v___x_8264_ =
                        l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(
                            v___x_8250_,
                            v___x_8263_,
                            v___y_8255_,
                            v___y_8256_,
                            v___y_8257_,
                        );
                    leanh::lean_dec(v___x_8263_);
                    if leanh::lean_obj_tag(v___x_8264_) == 0 {
                        v_a_8265_ = leanh::lean_ctor_get(v___x_8264_, 0);
                        leanh::lean_inc(v_a_8265_);
                        leanh::lean_dec_ref_known(v___x_8264_, 1);
                        v_snd_8266_ = leanh::lean_ctor_get(v_a_8265_, 1);
                        leanh::lean_inc(v_snd_8266_);
                        leanh::lean_dec(v_a_8265_);
                        v___x_8267_ = leanh::lean_box(0);
                        v___x_8268_ = 1usize;
                        v___x_8269_ = lean_usize_add(v_i_8253_, v___x_8268_);
                        v_i_8253_ = v___x_8269_;
                        v_b_8254_ = v___x_8267_;
                        v___y_8255_ = v_snd_8266_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___x_8250_);
                        return v___x_8264_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3___boxed(
    mut v___x_8271_: *mut leanh::LeanObject,
    mut v_as_8272_: *mut leanh::LeanObject,
    mut v_sz_8273_: *mut leanh::LeanObject,
    mut v_i_8274_: *mut leanh::LeanObject,
    mut v_b_8275_: *mut leanh::LeanObject,
    mut v___y_8276_: *mut leanh::LeanObject,
    mut v___y_8277_: *mut leanh::LeanObject,
    mut v___y_8278_: *mut leanh::LeanObject,
    mut v___y_8279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_8280_: usize = 0;
    let mut v_i_boxed_8281_: usize = 0;
    let mut v_res_8282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_8280_ = leanh::lean_unbox_usize(v_sz_8273_);
    leanh::lean_dec(v_sz_8273_);
    v_i_boxed_8281_ = leanh::lean_unbox_usize(v_i_8274_);
    leanh::lean_dec(v_i_8274_);
    v_res_8282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v___x_8271_, v_as_8272_, v_sz_boxed_8280_, v_i_boxed_8281_, v_b_8275_, v___y_8276_, v___y_8277_, v___y_8278_);
    leanh::lean_dec(v___y_8278_);
    leanh::lean_dec_ref(v___y_8277_);
    leanh::lean_dec_ref(v_as_8272_);
    return v_res_8282_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(
    mut v_a_8283_: *mut leanh::LeanObject,
    mut v_a_8284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_8286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_8287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8290_: u8 = 0;
    let mut v___x_8291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8296_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_8283_) == 0 {
                    v___x_8285_ = l_List_reverse___redArg(v_a_8284_);
                    return v___x_8285_;
                } else {
                    v_head_8286_ = leanh::lean_ctor_get(v_a_8283_, 0);
                    v_tail_8287_ = leanh::lean_ctor_get(v_a_8283_, 1);
                    v_isSharedCheck_8296_ = (!leanh::lean_is_exclusive(v_a_8283_)) as u8;
                    if v_isSharedCheck_8296_ == 0 {
                        v___x_8289_ = v_a_8283_;
                        v_isShared_8290_ = v_isSharedCheck_8296_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_8287_);
                        leanh::lean_inc(v_head_8286_);
                        leanh::lean_dec(v_a_8283_);
                        v___x_8289_ = leanh::lean_box(0);
                        v_isShared_8290_ = v_isSharedCheck_8296_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8291_ = l_Lean_MessageData_ofExpr(v_head_8286_);
                if v_isShared_8290_ == 0 {
                    leanh::lean_ctor_set(v___x_8289_, 1, v_a_8284_);
                    leanh::lean_ctor_set(v___x_8289_, 0, v___x_8291_);
                    v___x_8293_ = v___x_8289_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8295_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8295_, 0, v___x_8291_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8295_, 1, v_a_8284_);
                    v___x_8293_ = v_reuseFailAlloc_8295_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_8283_ = v_tail_8287_;
                v_a_8284_ = v___x_8293_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_spec__1___redArg(
    mut v_a_8297_: *mut leanh::LeanObject,
    mut v_b_8298_: *mut leanh::LeanObject,
    mut v_x_8299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_8300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_8301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_8302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8305_: u8 = 0;
    let mut v___x_8306_: u8 = 0;
    let mut v___x_8307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8314_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_8299_) == 0 {
                    leanh::lean_dec(v_b_8298_);
                    leanh::lean_dec(v_a_8297_);
                    return v_x_8299_;
                } else {
                    v_key_8300_ = leanh::lean_ctor_get(v_x_8299_, 0);
                    v_value_8301_ = leanh::lean_ctor_get(v_x_8299_, 1);
                    v_tail_8302_ = leanh::lean_ctor_get(v_x_8299_, 2);
                    v_isSharedCheck_8314_ = (!leanh::lean_is_exclusive(v_x_8299_)) as u8;
                    if v_isSharedCheck_8314_ == 0 {
                        v___x_8304_ = v_x_8299_;
                        v_isShared_8305_ = v_isSharedCheck_8314_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_8302_);
                        leanh::lean_inc(v_value_8301_);
                        leanh::lean_inc(v_key_8300_);
                        leanh::lean_dec(v_x_8299_);
                        v___x_8304_ = leanh::lean_box(0);
                        v_isShared_8305_ = v_isSharedCheck_8314_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8306_ = l_Lean_instBEqFVarId_beq(v_key_8300_, v_a_8297_);
                if v___x_8306_ == 0 {
                    v___x_8307_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_spec__1___redArg(v_a_8297_, v_b_8298_, v_tail_8302_);
                    if v_isShared_8305_ == 0 {
                        leanh::lean_ctor_set(v___x_8304_, 2, v___x_8307_);
                        v___x_8309_ = v___x_8304_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8310_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8310_, 0, v_key_8300_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8310_, 1, v_value_8301_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8310_, 2, v___x_8307_);
                        v___x_8309_ = v_reuseFailAlloc_8310_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_8301_);
                    leanh::lean_dec(v_key_8300_);
                    if v_isShared_8305_ == 0 {
                        leanh::lean_ctor_set(v___x_8304_, 1, v_b_8298_);
                        leanh::lean_ctor_set(v___x_8304_, 0, v_a_8297_);
                        v___x_8312_ = v___x_8304_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_8313_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8313_, 0, v_a_8297_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8313_, 1, v_b_8298_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8313_, 2, v_tail_8302_);
                        v___x_8312_ = v_reuseFailAlloc_8313_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_8309_;
            }
            3 => {
                return v___x_8312_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___redArg(
    mut v_m_8315_: *mut leanh::LeanObject,
    mut v_a_8316_: *mut leanh::LeanObject,
    mut v_b_8317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_8318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_8319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8322_: u8 = 0;
    let mut v___x_8323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8324_: u64 = 0;
    let mut v___x_8325_: u64 = 0;
    let mut v___x_8326_: u64 = 0;
    let mut v_fold_8327_: u64 = 0;
    let mut v___x_8328_: u64 = 0;
    let mut v___x_8329_: u64 = 0;
    let mut v___x_8330_: u64 = 0;
    let mut v___x_8331_: usize = 0;
    let mut v___x_8332_: usize = 0;
    let mut v___x_8333_: usize = 0;
    let mut v___x_8334_: usize = 0;
    let mut v___x_8335_: usize = 0;
    let mut v_bkt_8336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8337_: u8 = 0;
    let mut v___x_8338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_8339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_8341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8347_: u8 = 0;
    let mut v_val_8348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_8356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8362_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_8318_ = leanh::lean_ctor_get(v_m_8315_, 0);
                v_buckets_8319_ = leanh::lean_ctor_get(v_m_8315_, 1);
                v_isSharedCheck_8362_ = (!leanh::lean_is_exclusive(v_m_8315_)) as u8;
                if v_isSharedCheck_8362_ == 0 {
                    v___x_8321_ = v_m_8315_;
                    v_isShared_8322_ = v_isSharedCheck_8362_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_8319_);
                    leanh::lean_inc(v_size_8318_);
                    leanh::lean_dec(v_m_8315_);
                    v___x_8321_ = leanh::lean_box(0);
                    v_isShared_8322_ = v_isSharedCheck_8362_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8323_ = lean_array_get_size(v_buckets_8319_);
                v___x_8324_ = l_Lean_instHashableFVarId_hash(v_a_8316_);
                v___x_8325_ = 32u64;
                v___x_8326_ = lean_uint64_shift_right(v___x_8324_, v___x_8325_);
                v_fold_8327_ = lean_uint64_xor(v___x_8324_, v___x_8326_);
                v___x_8328_ = 16u64;
                v___x_8329_ = lean_uint64_shift_right(v_fold_8327_, v___x_8328_);
                v___x_8330_ = lean_uint64_xor(v_fold_8327_, v___x_8329_);
                v___x_8331_ = lean_uint64_to_usize(v___x_8330_);
                v___x_8332_ = lean_usize_of_nat(v___x_8323_);
                v___x_8333_ = 1usize;
                v___x_8334_ = lean_usize_sub(v___x_8332_, v___x_8333_);
                v___x_8335_ = lean_usize_land(v___x_8331_, v___x_8334_);
                v_bkt_8336_ = lean_array_uget_borrowed(v_buckets_8319_, v___x_8335_);
                v___x_8337_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_8316_, v_bkt_8336_);
                if v___x_8337_ == 0 {
                    v___x_8338_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_8339_ = lean_nat_add(v_size_8318_, v___x_8338_);
                    leanh::lean_dec(v_size_8318_);
                    leanh::lean_inc(v_bkt_8336_);
                    v___x_8340_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_8340_, 0, v_a_8316_);
                    leanh::lean_ctor_set(v___x_8340_, 1, v_b_8317_);
                    leanh::lean_ctor_set(v___x_8340_, 2, v_bkt_8336_);
                    v_buckets_x27_8341_ =
                        lean_array_uset(v_buckets_8319_, v___x_8335_, v___x_8340_);
                    v___x_8342_ = leanh::lean_unsigned_to_nat(4);
                    v___x_8343_ = lean_nat_mul(v_size_x27_8339_, v___x_8342_);
                    v___x_8344_ = leanh::lean_unsigned_to_nat(3);
                    v___x_8345_ = lean_nat_div(v___x_8343_, v___x_8344_);
                    leanh::lean_dec(v___x_8343_);
                    v___x_8346_ = lean_array_get_size(v_buckets_x27_8341_);
                    v___x_8347_ = lean_nat_dec_le(v___x_8345_, v___x_8346_);
                    leanh::lean_dec(v___x_8345_);
                    if v___x_8347_ == 0 {
                        v_val_8348_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_buckets_x27_8341_);
                        if v_isShared_8322_ == 0 {
                            leanh::lean_ctor_set(v___x_8321_, 1, v_val_8348_);
                            leanh::lean_ctor_set(v___x_8321_, 0, v_size_x27_8339_);
                            v___x_8350_ = v___x_8321_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_8351_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_8351_,
                                0,
                                v_size_x27_8339_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_8351_, 1, v_val_8348_);
                            v___x_8350_ = v_reuseFailAlloc_8351_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_8322_ == 0 {
                            leanh::lean_ctor_set(v___x_8321_, 1, v_buckets_x27_8341_);
                            leanh::lean_ctor_set(v___x_8321_, 0, v_size_x27_8339_);
                            v___x_8353_ = v___x_8321_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_8354_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_8354_,
                                0,
                                v_size_x27_8339_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_8354_,
                                1,
                                v_buckets_x27_8341_,
                            );
                            v___x_8353_ = v_reuseFailAlloc_8354_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_8336_);
                    v___x_8355_ = leanh::lean_box(0);
                    v_buckets_x27_8356_ =
                        lean_array_uset(v_buckets_8319_, v___x_8335_, v___x_8355_);
                    v___x_8357_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_spec__1___redArg(v_a_8316_, v_b_8317_, v_bkt_8336_);
                    v___x_8358_ = lean_array_uset(v_buckets_x27_8356_, v___x_8335_, v___x_8357_);
                    if v_isShared_8322_ == 0 {
                        leanh::lean_ctor_set(v___x_8321_, 1, v___x_8358_);
                        v___x_8360_ = v___x_8321_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_8361_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8361_, 0, v_size_8318_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8361_, 1, v___x_8358_);
                        v___x_8360_ = v_reuseFailAlloc_8361_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_8350_;
            }
            3 => {
                return v___x_8353_;
            }
            4 => {
                return v___x_8360_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(
    mut v_as_8363_: *mut leanh::LeanObject,
    mut v_sz_8364_: usize,
    mut v_i_8365_: usize,
    mut v_b_8366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8368_: u8 = 0;
    let mut v___x_8369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_8371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8374_: u8 = 0;
    let mut v_array_8375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_8376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_8377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8378_: u8 = 0;
    let mut v___x_8380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8385_: u8 = 0;
    let mut v_a_8386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8397_: usize = 0;
    let mut v___x_8398_: usize = 0;
    let mut v_reuseFailAlloc_8400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8402_: u8 = 0;
    let mut v_unused_8403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8406_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8368_ = lean_usize_dec_lt(v_i_8365_, v_sz_8364_);
                if v___x_8368_ == 0 {
                    v___x_8369_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8369_, 0, v_b_8366_);
                    return v___x_8369_;
                } else {
                    v_snd_8370_ = leanh::lean_ctor_get(v_b_8366_, 1);
                    v_fst_8371_ = leanh::lean_ctor_get(v_b_8366_, 0);
                    v_isSharedCheck_8406_ = (!leanh::lean_is_exclusive(v_b_8366_)) as u8;
                    if v_isSharedCheck_8406_ == 0 {
                        v___x_8373_ = v_b_8366_;
                        v_isShared_8374_ = v_isSharedCheck_8406_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_8370_);
                        leanh::lean_inc(v_fst_8371_);
                        leanh::lean_dec(v_b_8366_);
                        v___x_8373_ = leanh::lean_box(0);
                        v_isShared_8374_ = v_isSharedCheck_8406_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_array_8375_ = leanh::lean_ctor_get(v_snd_8370_, 0);
                v_start_8376_ = leanh::lean_ctor_get(v_snd_8370_, 1);
                v_stop_8377_ = leanh::lean_ctor_get(v_snd_8370_, 2);
                v___x_8378_ = lean_nat_dec_lt(v_start_8376_, v_stop_8377_);
                if v___x_8378_ == 0 {
                    if v_isShared_8374_ == 0 {
                        v___x_8380_ = v___x_8373_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8382_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8382_, 0, v_fst_8371_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8382_, 1, v_snd_8370_);
                        v___x_8380_ = v_reuseFailAlloc_8382_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_stop_8377_);
                    leanh::lean_inc(v_start_8376_);
                    leanh::lean_inc_ref(v_array_8375_);
                    v_isSharedCheck_8402_ = (!leanh::lean_is_exclusive(v_snd_8370_)) as u8;
                    if v_isSharedCheck_8402_ == 0 {
                        v_unused_8403_ = leanh::lean_ctor_get(v_snd_8370_, 2);
                        leanh::lean_dec(v_unused_8403_);
                        v_unused_8404_ = leanh::lean_ctor_get(v_snd_8370_, 1);
                        leanh::lean_dec(v_unused_8404_);
                        v_unused_8405_ = leanh::lean_ctor_get(v_snd_8370_, 0);
                        leanh::lean_dec(v_unused_8405_);
                        v___x_8384_ = v_snd_8370_;
                        v_isShared_8385_ = v_isSharedCheck_8402_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_snd_8370_);
                        v___x_8384_ = leanh::lean_box(0);
                        v_isShared_8385_ = v_isSharedCheck_8402_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_8381_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_8381_, 0, v___x_8380_);
                return v___x_8381_;
            }
            3 => {
                v_a_8386_ = lean_array_uget_borrowed(v_as_8363_, v_i_8365_);
                v___x_8387_ = lean_array_fget(v_array_8375_, v_start_8376_);
                v___x_8388_ = leanh::lean_unsigned_to_nat(1);
                v___x_8389_ = lean_nat_add(v_start_8376_, v___x_8388_);
                leanh::lean_dec(v_start_8376_);
                if v_isShared_8385_ == 0 {
                    leanh::lean_ctor_set(v___x_8384_, 1, v___x_8389_);
                    v___x_8391_ = v___x_8384_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8401_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8401_, 0, v_array_8375_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8401_, 1, v___x_8389_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8401_, 2, v_stop_8377_);
                    v___x_8391_ = v_reuseFailAlloc_8401_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_8392_ = l_Lean_LocalDecl_fvarId(v_a_8386_);
                leanh::lean_inc(v_a_8386_);
                if v_isShared_8374_ == 0 {
                    leanh::lean_ctor_set(v___x_8373_, 1, v___x_8387_);
                    leanh::lean_ctor_set(v___x_8373_, 0, v_a_8386_);
                    v___x_8394_ = v___x_8373_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8400_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8400_, 0, v_a_8386_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8400_, 1, v___x_8387_);
                    v___x_8394_ = v_reuseFailAlloc_8400_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_8395_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___redArg(v_fst_8371_, v___x_8392_, v___x_8394_);
                v___x_8396_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8396_, 0, v___x_8395_);
                leanh::lean_ctor_set(v___x_8396_, 1, v___x_8391_);
                v___x_8397_ = 1usize;
                v___x_8398_ = lean_usize_add(v_i_8365_, v___x_8397_);
                v_i_8365_ = v___x_8398_;
                v_b_8366_ = v___x_8396_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg___boxed(
    mut v_as_8407_: *mut leanh::LeanObject,
    mut v_sz_8408_: *mut leanh::LeanObject,
    mut v_i_8409_: *mut leanh::LeanObject,
    mut v_b_8410_: *mut leanh::LeanObject,
    mut v___y_8411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_8412_: usize = 0;
    let mut v_i_boxed_8413_: usize = 0;
    let mut v_res_8414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_8412_ = leanh::lean_unbox_usize(v_sz_8408_);
    leanh::lean_dec(v_sz_8408_);
    v_i_boxed_8413_ = leanh::lean_unbox_usize(v_i_8409_);
    leanh::lean_dec(v_i_8409_);
    v_res_8414_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_as_8407_, v_sz_boxed_8412_, v_i_boxed_8413_, v_b_8410_);
    leanh::lean_dec_ref(v_as_8407_);
    return v_res_8414_;
}
pub unsafe fn _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_8417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8417_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__1;
    v___x_8418_ = leanh::lean_unsigned_to_nat(2);
    v___x_8419_ = leanh::lean_unsigned_to_nat(366);
    v___x_8420_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0;
    v___x_8421_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2;
    v___x_8422_ = l_mkPanicMessageWithDecl(
        v___x_8421_,
        v___x_8420_,
        v___x_8419_,
        v___x_8418_,
        v___x_8417_,
    );
    return v___x_8422_;
}
pub unsafe fn _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_8424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8424_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__3;
    v___x_8425_ = leanh::lean_unsigned_to_nat(2);
    v___x_8426_ = leanh::lean_unsigned_to_nat(367);
    v___x_8427_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0;
    v___x_8428_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2;
    v___x_8429_ = l_mkPanicMessageWithDecl(
        v___x_8428_,
        v___x_8427_,
        v___x_8426_,
        v___x_8425_,
        v___x_8424_,
    );
    return v___x_8429_;
}
pub unsafe fn _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_8430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8430_ = leanh::lean_box(0);
    v___x_8431_ = leanh::lean_unsigned_to_nat(16);
    v___x_8432_ = lean_mk_array(v___x_8431_, v___x_8430_);
    return v___x_8432_;
}
pub unsafe fn _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_8433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8433_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5_once
        ),
        _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5,
    );
    v___x_8434_ = leanh::lean_unsigned_to_nat(0);
    v___x_8435_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_8435_, 0, v___x_8434_);
    leanh::lean_ctor_set(v___x_8435_, 1, v___x_8433_);
    return v___x_8435_;
}
pub unsafe fn _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_8437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8437_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__7;
    v___x_8438_ = l_Lean_stringToMessageData(v___x_8437_);
    return v___x_8438_;
}
pub unsafe fn _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_8440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8440_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__9;
    v___x_8441_ = l_Lean_stringToMessageData(v___x_8440_);
    return v___x_8441_;
}
pub unsafe fn l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(
    mut v_sortedDecls_8442_: *mut leanh::LeanObject,
    mut v_sortedArgs_8443_: *mut leanh::LeanObject,
    mut v_toSortDecls_8444_: *mut leanh::LeanObject,
    mut v_toSortArgs_8445_: *mut leanh::LeanObject,
    mut v_a_8446_: *mut leanh::LeanObject,
    mut v_a_8447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_8450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8454_: u8 = 0;
    let mut v_fst_8455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8459_: u8 = 0;
    let mut v_a_8460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8463_: u8 = 0;
    let mut v___x_8465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8467_: u8 = 0;
    let mut v___y_8469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8477_: u8 = 0;
    let mut v___x_8478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8482_: u8 = 0;
    let mut v___x_8483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8486_: u8 = 0;
    let mut v_options_8487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_8488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_8489_: u8 = 0;
    let mut v_cls_8490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_8497_: usize = 0;
    let mut v___x_8498_: usize = 0;
    let mut v___x_8499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_8501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8504_: u8 = 0;
    let mut v___x_8505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_8508_: usize = 0;
    let mut v___x_8509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_8511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8525_: u8 = 0;
    let mut v_options_8526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newDecls_8527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newArgs_8528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_8529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_8530_: u8 = 0;
    let mut v___f_8531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8533_: u8 = 0;
    let mut v___x_8534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_8535_: usize = 0;
    let mut v___x_8536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_8545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8551_: u8 = 0;
    let mut v___x_8553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8555_: u8 = 0;
    let mut v_reuseFailAlloc_8556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8557_: u8 = 0;
    let mut v_unused_8558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8562_: u8 = 0;
    let mut v___x_8564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8566_: u8 = 0;
    let mut v_a_8567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8570_: u8 = 0;
    let mut v___x_8572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8574_: u8 = 0;
    let mut v_a_8575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8578_: u8 = 0;
    let mut v___x_8580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8582_: u8 = 0;
    let mut v_reuseFailAlloc_8583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8584_: u8 = 0;
    let mut v_unused_8585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8589_: u8 = 0;
    let mut v___x_8591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8593_: u8 = 0;
    let mut v___x_8594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8595_: u8 = 0;
    let mut v___x_8596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8601_: u8 = 0;
    let mut v___x_8603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8605_: u8 = 0;
    let mut v___x_8606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8475_ = lean_array_get_size(v_sortedDecls_8442_);
                v___x_8476_ = lean_array_get_size(v_sortedArgs_8443_);
                v___x_8477_ = lean_nat_dec_eq(v___x_8475_, v___x_8476_);
                if v___x_8477_ == 0 {
                    leanh::lean_dec_ref(v_toSortArgs_8445_);
                    leanh::lean_dec_ref(v_sortedArgs_8443_);
                    leanh::lean_dec_ref(v_sortedDecls_8442_);
                    v___x_8478_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2_once), _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2);
                    v___x_8479_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(v___x_8478_, v_a_8446_, v_a_8447_);
                    return v___x_8479_;
                } else {
                    v___x_8480_ = lean_array_get_size(v_toSortDecls_8444_);
                    v___x_8481_ = lean_array_get_size(v_toSortArgs_8445_);
                    v___x_8482_ = lean_nat_dec_eq(v___x_8480_, v___x_8481_);
                    if v___x_8482_ == 0 {
                        leanh::lean_dec_ref(v_toSortArgs_8445_);
                        leanh::lean_dec_ref(v_sortedArgs_8443_);
                        leanh::lean_dec_ref(v_sortedDecls_8442_);
                        v___x_8483_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4_once), _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4);
                        v___x_8484_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(v___x_8483_, v_a_8446_, v_a_8447_);
                        return v___x_8484_;
                    } else {
                        v___x_8485_ = leanh::lean_unsigned_to_nat(0);
                        v___x_8486_ = lean_nat_dec_eq(v___x_8480_, v___x_8485_);
                        if v___x_8486_ == 0 {
                            v_options_8487_ = leanh::lean_ctor_get(v_a_8446_, 2);
                            v_inheritedTraceOptions_8488_ =
                                leanh::lean_ctor_get(v_a_8446_, 13);
                            v_hasTrace_8489_ = leanh::lean_ctor_get_uint8(
                                v_options_8487_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            );
                            v_cls_8490_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10;
                            if v_hasTrace_8489_ == 0 {
                                v___y_8492_ = v_a_8446_;
                                v___y_8493_ = v_a_8447_;
                                state = 7;
                                continue;
                            } else {
                                v___x_8594_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once), _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
                                v___x_8595_ =
                                    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                        v_inheritedTraceOptions_8488_,
                                        v_options_8487_,
                                        v___x_8594_,
                                    );
                                if v___x_8595_ == 0 {
                                    v___y_8492_ = v_a_8446_;
                                    v___y_8493_ = v_a_8447_;
                                    state = 7;
                                    continue;
                                } else {
                                    v___x_8596_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10_once), _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10);
                                    v___x_8597_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(v_cls_8490_, v___x_8596_, v_a_8446_, v_a_8447_);
                                    if leanh::lean_obj_tag(v___x_8597_) == 0 {
                                        leanh::lean_dec_ref_known(v___x_8597_, 1);
                                        v___y_8492_ = v_a_8446_;
                                        v___y_8493_ = v_a_8447_;
                                        state = 7;
                                        continue;
                                    } else {
                                        leanh::lean_dec_ref(v_toSortArgs_8445_);
                                        leanh::lean_dec_ref(v_sortedArgs_8443_);
                                        leanh::lean_dec_ref(v_sortedDecls_8442_);
                                        v_a_8598_ = leanh::lean_ctor_get(v___x_8597_, 0);
                                        v_isSharedCheck_8605_ =
                                            (!leanh::lean_is_exclusive(v___x_8597_)) as u8;
                                        if v_isSharedCheck_8605_ == 0 {
                                            v___x_8600_ = v___x_8597_;
                                            v_isShared_8601_ = v_isSharedCheck_8605_;
                                            state = 22;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_8598_);
                                            leanh::lean_dec(v___x_8597_);
                                            v___x_8600_ = leanh::lean_box(0);
                                            v_isShared_8601_ = v_isSharedCheck_8605_;
                                            state = 22;
                                            continue;
                                        }
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_toSortArgs_8445_);
                            v___x_8606_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_8606_, 0, v_sortedDecls_8442_);
                            leanh::lean_ctor_set(v___x_8606_, 1, v_sortedArgs_8443_);
                            v___x_8607_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_8607_, 0, v___x_8606_);
                            return v___x_8607_;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_8450_) == 0 {
                    v_a_8451_ = leanh::lean_ctor_get(v___y_8450_, 0);
                    v_isSharedCheck_8459_ = (!leanh::lean_is_exclusive(v___y_8450_)) as u8;
                    if v_isSharedCheck_8459_ == 0 {
                        v___x_8453_ = v___y_8450_;
                        v_isShared_8454_ = v_isSharedCheck_8459_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8451_);
                        leanh::lean_dec(v___y_8450_);
                        v___x_8453_ = leanh::lean_box(0);
                        v_isShared_8454_ = v_isSharedCheck_8459_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_8460_ = leanh::lean_ctor_get(v___y_8450_, 0);
                    v_isSharedCheck_8467_ = (!leanh::lean_is_exclusive(v___y_8450_)) as u8;
                    if v_isSharedCheck_8467_ == 0 {
                        v___x_8462_ = v___y_8450_;
                        v_isShared_8463_ = v_isSharedCheck_8467_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8460_);
                        leanh::lean_dec(v___y_8450_);
                        v___x_8462_ = leanh::lean_box(0);
                        v_isShared_8463_ = v_isSharedCheck_8467_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_8455_ = leanh::lean_ctor_get(v_a_8451_, 0);
                leanh::lean_inc(v_fst_8455_);
                leanh::lean_dec(v_a_8451_);
                if v_isShared_8454_ == 0 {
                    leanh::lean_ctor_set(v___x_8453_, 0, v_fst_8455_);
                    v___x_8457_ = v___x_8453_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8458_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8458_, 0, v_fst_8455_);
                    v___x_8457_ = v_reuseFailAlloc_8458_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_8457_;
            }
            4 => {
                if v_isShared_8463_ == 0 {
                    v___x_8465_ = v___x_8462_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8466_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8466_, 0, v_a_8460_);
                    v___x_8465_ = v_reuseFailAlloc_8466_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_8465_;
            }
            6 => {
                leanh::lean_inc(v___y_8471_);
                leanh::lean_inc_ref(v___y_8469_);
                v___x_8474_ = leanh::lean_apply_5(
                    v___y_8472_,
                    v___y_8470_,
                    v_snd_8473_,
                    v___y_8469_,
                    v___y_8471_,
                    leanh::lean_box(0),
                );
                v___y_8450_ = v___x_8474_;
                state = 1;
                continue;
            }
            7 => {
                v___x_8494_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6_once), _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6);
                v___x_8495_ =
                    l_Array_toSubarray___redArg(v_sortedArgs_8443_, v___x_8485_, v___x_8476_);
                v___x_8496_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8496_, 0, v___x_8494_);
                leanh::lean_ctor_set(v___x_8496_, 1, v___x_8495_);
                v_sz_8497_ = lean_array_size(v_sortedDecls_8442_);
                v___x_8498_ = 0usize;
                v___x_8499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_sortedDecls_8442_, v_sz_8497_, v___x_8498_, v___x_8496_);
                if leanh::lean_obj_tag(v___x_8499_) == 0 {
                    v_a_8500_ = leanh::lean_ctor_get(v___x_8499_, 0);
                    leanh::lean_inc(v_a_8500_);
                    leanh::lean_dec_ref_known(v___x_8499_, 1);
                    v_fst_8501_ = leanh::lean_ctor_get(v_a_8500_, 0);
                    v_isSharedCheck_8584_ = (!leanh::lean_is_exclusive(v_a_8500_)) as u8;
                    if v_isSharedCheck_8584_ == 0 {
                        v_unused_8585_ = leanh::lean_ctor_get(v_a_8500_, 1);
                        leanh::lean_dec(v_unused_8585_);
                        v___x_8503_ = v_a_8500_;
                        v_isShared_8504_ = v_isSharedCheck_8584_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_8501_);
                        leanh::lean_dec(v_a_8500_);
                        v___x_8503_ = leanh::lean_box(0);
                        v_isShared_8504_ = v_isSharedCheck_8584_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_toSortArgs_8445_);
                    leanh::lean_dec_ref(v_sortedDecls_8442_);
                    v_a_8586_ = leanh::lean_ctor_get(v___x_8499_, 0);
                    v_isSharedCheck_8593_ = (!leanh::lean_is_exclusive(v___x_8499_)) as u8;
                    if v_isSharedCheck_8593_ == 0 {
                        v___x_8588_ = v___x_8499_;
                        v_isShared_8589_ = v_isSharedCheck_8593_;
                        state = 20;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8586_);
                        leanh::lean_dec(v___x_8499_);
                        v___x_8588_ = leanh::lean_box(0);
                        v_isShared_8589_ = v_isSharedCheck_8593_;
                        state = 20;
                        continue;
                    }
                }
            }
            8 => {
                v___x_8505_ =
                    l_Array_toSubarray___redArg(v_toSortArgs_8445_, v___x_8485_, v___x_8481_);
                if v_isShared_8504_ == 0 {
                    leanh::lean_ctor_set(v___x_8503_, 1, v___x_8505_);
                    v___x_8507_ = v___x_8503_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8583_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8583_, 0, v_fst_8501_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8583_, 1, v___x_8505_);
                    v___x_8507_ = v_reuseFailAlloc_8583_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_sz_8508_ = lean_array_size(v_toSortDecls_8444_);
                v___x_8509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_toSortDecls_8444_, v_sz_8508_, v___x_8498_, v___x_8507_);
                if leanh::lean_obj_tag(v___x_8509_) == 0 {
                    v_a_8510_ = leanh::lean_ctor_get(v___x_8509_, 0);
                    leanh::lean_inc(v_a_8510_);
                    leanh::lean_dec_ref_known(v___x_8509_, 1);
                    v_fst_8511_ = leanh::lean_ctor_get(v_a_8510_, 0);
                    leanh::lean_inc_n(v_fst_8511_, 2);
                    leanh::lean_dec(v_a_8510_);
                    v_size_8512_ = leanh::lean_ctor_get(v_fst_8511_, 0);
                    v___x_8513_ = l_Lean_instEmptyCollectionFVarIdHashSet;
                    v___x_8514_ = lean_mk_empty_array_with_capacity(v_size_8512_);
                    leanh::lean_inc_ref(v___x_8514_);
                    v___x_8515_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_8515_, 0, v___x_8513_);
                    leanh::lean_ctor_set(v___x_8515_, 1, v___x_8513_);
                    leanh::lean_ctor_set(v___x_8515_, 2, v___x_8514_);
                    leanh::lean_ctor_set(v___x_8515_, 3, v___x_8514_);
                    v___x_8516_ = leanh::lean_box(0);
                    v___x_8517_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v_fst_8511_, v_sortedDecls_8442_, v_sz_8497_, v___x_8498_, v___x_8516_, v___x_8515_, v___y_8492_, v___y_8493_);
                    leanh::lean_dec_ref(v_sortedDecls_8442_);
                    if leanh::lean_obj_tag(v___x_8517_) == 0 {
                        v_a_8518_ = leanh::lean_ctor_get(v___x_8517_, 0);
                        leanh::lean_inc(v_a_8518_);
                        leanh::lean_dec_ref_known(v___x_8517_, 1);
                        v_snd_8519_ = leanh::lean_ctor_get(v_a_8518_, 1);
                        leanh::lean_inc(v_snd_8519_);
                        leanh::lean_dec(v_a_8518_);
                        v___x_8520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v_fst_8511_, v_toSortDecls_8444_, v_sz_8508_, v___x_8498_, v___x_8516_, v_snd_8519_, v___y_8492_, v___y_8493_);
                        if leanh::lean_obj_tag(v___x_8520_) == 0 {
                            v_a_8521_ = leanh::lean_ctor_get(v___x_8520_, 0);
                            leanh::lean_inc(v_a_8521_);
                            leanh::lean_dec_ref_known(v___x_8520_, 1);
                            v_snd_8522_ = leanh::lean_ctor_get(v_a_8521_, 1);
                            v_isSharedCheck_8557_ =
                                (!leanh::lean_is_exclusive(v_a_8521_)) as u8;
                            if v_isSharedCheck_8557_ == 0 {
                                v_unused_8558_ = leanh::lean_ctor_get(v_a_8521_, 0);
                                leanh::lean_dec(v_unused_8558_);
                                v___x_8524_ = v_a_8521_;
                                v_isShared_8525_ = v_isSharedCheck_8557_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_8522_);
                                leanh::lean_dec(v_a_8521_);
                                v___x_8524_ = leanh::lean_box(0);
                                v_isShared_8525_ = v_isSharedCheck_8557_;
                                state = 10;
                                continue;
                            }
                        } else {
                            v_a_8559_ = leanh::lean_ctor_get(v___x_8520_, 0);
                            v_isSharedCheck_8566_ =
                                (!leanh::lean_is_exclusive(v___x_8520_)) as u8;
                            if v_isSharedCheck_8566_ == 0 {
                                v___x_8561_ = v___x_8520_;
                                v_isShared_8562_ = v_isSharedCheck_8566_;
                                state = 14;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_8559_);
                                leanh::lean_dec(v___x_8520_);
                                v___x_8561_ = leanh::lean_box(0);
                                v_isShared_8562_ = v_isSharedCheck_8566_;
                                state = 14;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_fst_8511_);
                        v_a_8567_ = leanh::lean_ctor_get(v___x_8517_, 0);
                        v_isSharedCheck_8574_ =
                            (!leanh::lean_is_exclusive(v___x_8517_)) as u8;
                        if v_isSharedCheck_8574_ == 0 {
                            v___x_8569_ = v___x_8517_;
                            v_isShared_8570_ = v_isSharedCheck_8574_;
                            state = 16;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_8567_);
                            leanh::lean_dec(v___x_8517_);
                            v___x_8569_ = leanh::lean_box(0);
                            v_isShared_8570_ = v_isSharedCheck_8574_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_sortedDecls_8442_);
                    v_a_8575_ = leanh::lean_ctor_get(v___x_8509_, 0);
                    v_isSharedCheck_8582_ = (!leanh::lean_is_exclusive(v___x_8509_)) as u8;
                    if v_isSharedCheck_8582_ == 0 {
                        v___x_8577_ = v___x_8509_;
                        v_isShared_8578_ = v_isSharedCheck_8582_;
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8575_);
                        leanh::lean_dec(v___x_8509_);
                        v___x_8577_ = leanh::lean_box(0);
                        v_isShared_8578_ = v_isSharedCheck_8582_;
                        state = 18;
                        continue;
                    }
                }
            }
            10 => {
                v_options_8526_ = leanh::lean_ctor_get(v___y_8492_, 2);
                v_newDecls_8527_ = leanh::lean_ctor_get(v_snd_8522_, 2);
                v_newArgs_8528_ = leanh::lean_ctor_get(v_snd_8522_, 3);
                v_inheritedTraceOptions_8529_ = leanh::lean_ctor_get(v___y_8492_, 13);
                v_hasTrace_8530_ = leanh::lean_ctor_get_uint8(
                    v_options_8526_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                leanh::lean_inc_ref(v_newArgs_8528_);
                leanh::lean_inc_ref(v_newDecls_8527_);
                v___f_8531_ = leanh::lean_alloc_closure(
                    l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0___boxed
                        as *mut core::ffi::c_void,
                    7,
                    2,
                );
                leanh::lean_closure_set(v___f_8531_, 0, v_newDecls_8527_);
                leanh::lean_closure_set(v___f_8531_, 1, v_newArgs_8528_);
                if v_hasTrace_8530_ == 0 {
                    leanh::lean_del_object(v___x_8524_);
                    v___y_8469_ = v___y_8492_;
                    v___y_8470_ = v___x_8516_;
                    v___y_8471_ = v___y_8493_;
                    v___y_8472_ = v___f_8531_;
                    v_snd_8473_ = v_snd_8522_;
                    state = 6;
                    continue;
                } else {
                    v___x_8532_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once), _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
                    v___x_8533_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_8529_,
                        v_options_8526_,
                        v___x_8532_,
                    );
                    if v___x_8533_ == 0 {
                        leanh::lean_del_object(v___x_8524_);
                        v___y_8469_ = v___y_8492_;
                        v___y_8470_ = v___x_8516_;
                        v___y_8471_ = v___y_8493_;
                        v___y_8472_ = v___f_8531_;
                        v_snd_8473_ = v_snd_8522_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc_ref(v_newArgs_8528_);
                        leanh::lean_inc_ref_n(v_newDecls_8527_, 2);
                        leanh::lean_dec_ref(v___f_8531_);
                        v___x_8534_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8_once), _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8);
                        v_sz_8535_ = lean_array_size(v_newDecls_8527_);
                        v___x_8536_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(v_sz_8535_, v___x_8498_, v_newDecls_8527_);
                        v___x_8537_ = lean_array_to_list(v___x_8536_);
                        v___x_8538_ = leanh::lean_box(0);
                        v___x_8539_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(v___x_8537_, v___x_8538_);
                        v___x_8540_ = l_Lean_MessageData_ofList(v___x_8539_);
                        if v_isShared_8525_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_8524_, 7);
                            leanh::lean_ctor_set(v___x_8524_, 1, v___x_8540_);
                            leanh::lean_ctor_set(v___x_8524_, 0, v___x_8534_);
                            v___x_8542_ = v___x_8524_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_8556_ =
                                leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_8556_, 0, v___x_8534_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_8556_, 1, v___x_8540_);
                            v___x_8542_ = v_reuseFailAlloc_8556_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            11 => {
                v___x_8543_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v_cls_8490_, v___x_8542_, v_snd_8522_, v___y_8492_, v___y_8493_);
                if leanh::lean_obj_tag(v___x_8543_) == 0 {
                    v_a_8544_ = leanh::lean_ctor_get(v___x_8543_, 0);
                    leanh::lean_inc(v_a_8544_);
                    leanh::lean_dec_ref_known(v___x_8543_, 1);
                    v_fst_8545_ = leanh::lean_ctor_get(v_a_8544_, 0);
                    leanh::lean_inc(v_fst_8545_);
                    v_snd_8546_ = leanh::lean_ctor_get(v_a_8544_, 1);
                    leanh::lean_inc(v_snd_8546_);
                    leanh::lean_dec(v_a_8544_);
                    v___x_8547_ =
                        l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(
                            v_newDecls_8527_,
                            v_newArgs_8528_,
                            v_fst_8545_,
                            v_snd_8546_,
                            v___y_8492_,
                            v___y_8493_,
                        );
                    v___y_8450_ = v___x_8547_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_newArgs_8528_);
                    leanh::lean_dec_ref(v_newDecls_8527_);
                    v_a_8548_ = leanh::lean_ctor_get(v___x_8543_, 0);
                    v_isSharedCheck_8555_ = (!leanh::lean_is_exclusive(v___x_8543_)) as u8;
                    if v_isSharedCheck_8555_ == 0 {
                        v___x_8550_ = v___x_8543_;
                        v_isShared_8551_ = v_isSharedCheck_8555_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8548_);
                        leanh::lean_dec(v___x_8543_);
                        v___x_8550_ = leanh::lean_box(0);
                        v_isShared_8551_ = v_isSharedCheck_8555_;
                        state = 12;
                        continue;
                    }
                }
            }
            12 => {
                if v_isShared_8551_ == 0 {
                    v___x_8553_ = v___x_8550_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_8554_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8554_, 0, v_a_8548_);
                    v___x_8553_ = v_reuseFailAlloc_8554_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_8553_;
            }
            14 => {
                if v_isShared_8562_ == 0 {
                    v___x_8564_ = v___x_8561_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_8565_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8565_, 0, v_a_8559_);
                    v___x_8564_ = v_reuseFailAlloc_8565_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_8564_;
            }
            16 => {
                if v_isShared_8570_ == 0 {
                    v___x_8572_ = v___x_8569_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_8573_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8573_, 0, v_a_8567_);
                    v___x_8572_ = v_reuseFailAlloc_8573_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_8572_;
            }
            18 => {
                if v_isShared_8578_ == 0 {
                    v___x_8580_ = v___x_8577_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_8581_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8581_, 0, v_a_8575_);
                    v___x_8580_ = v_reuseFailAlloc_8581_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_8580_;
            }
            20 => {
                if v_isShared_8589_ == 0 {
                    v___x_8591_ = v___x_8588_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_8592_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8592_, 0, v_a_8586_);
                    v___x_8591_ = v_reuseFailAlloc_8592_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_8591_;
            }
            22 => {
                if v_isShared_8601_ == 0 {
                    v___x_8603_ = v___x_8600_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_8604_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8604_, 0, v_a_8598_);
                    v___x_8603_ = v_reuseFailAlloc_8604_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_8603_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___boxed(
    mut v_sortedDecls_8608_: *mut leanh::LeanObject,
    mut v_sortedArgs_8609_: *mut leanh::LeanObject,
    mut v_toSortDecls_8610_: *mut leanh::LeanObject,
    mut v_toSortArgs_8611_: *mut leanh::LeanObject,
    mut v_a_8612_: *mut leanh::LeanObject,
    mut v_a_8613_: *mut leanh::LeanObject,
    mut v_a_8614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8615_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(
        v_sortedDecls_8608_,
        v_sortedArgs_8609_,
        v_toSortDecls_8610_,
        v_toSortArgs_8611_,
        v_a_8612_,
        v_a_8613_,
    );
    leanh::lean_dec(v_a_8613_);
    leanh::lean_dec_ref(v_a_8612_);
    leanh::lean_dec_ref(v_toSortDecls_8610_);
    return v_res_8615_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(
    mut v_00_u03b2_8616_: *mut leanh::LeanObject,
    mut v_m_8617_: *mut leanh::LeanObject,
    mut v_a_8618_: *mut leanh::LeanObject,
    mut v_b_8619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8620_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___redArg(v_m_8617_, v_a_8618_, v_b_8619_);
    return v___x_8620_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(
    mut v_as_8621_: *mut leanh::LeanObject,
    mut v_sz_8622_: usize,
    mut v_i_8623_: usize,
    mut v_b_8624_: *mut leanh::LeanObject,
    mut v___y_8625_: *mut leanh::LeanObject,
    mut v___y_8626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_as_8621_, v_sz_8622_, v_i_8623_, v_b_8624_);
    return v___x_8628_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___boxed(
    mut v_as_8629_: *mut leanh::LeanObject,
    mut v_sz_8630_: *mut leanh::LeanObject,
    mut v_i_8631_: *mut leanh::LeanObject,
    mut v_b_8632_: *mut leanh::LeanObject,
    mut v___y_8633_: *mut leanh::LeanObject,
    mut v___y_8634_: *mut leanh::LeanObject,
    mut v___y_8635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_8636_: usize = 0;
    let mut v_i_boxed_8637_: usize = 0;
    let mut v_res_8638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_8636_ = leanh::lean_unbox_usize(v_sz_8630_);
    leanh::lean_dec(v_sz_8630_);
    v_i_boxed_8637_ = leanh::lean_unbox_usize(v_i_8631_);
    leanh::lean_dec(v_i_8631_);
    v_res_8638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(v_as_8629_, v_sz_boxed_8636_, v_i_boxed_8637_, v_b_8632_, v___y_8633_, v___y_8634_);
    leanh::lean_dec(v___y_8634_);
    leanh::lean_dec_ref(v___y_8633_);
    leanh::lean_dec_ref(v_as_8629_);
    return v_res_8638_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_spec__1(
    mut v_00_u03b2_8639_: *mut leanh::LeanObject,
    mut v_a_8640_: *mut leanh::LeanObject,
    mut v_b_8641_: *mut leanh::LeanObject,
    mut v_x_8642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8643_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_spec__1___redArg(v_a_8640_, v_b_8641_, v_x_8642_);
    return v___x_8643_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(
    mut v_msg_8645_: *mut leanh::LeanObject,
    mut v___y_8646_: *mut leanh::LeanObject,
    mut v___y_8647_: *mut leanh::LeanObject,
    mut v___y_8648_: *mut leanh::LeanObject,
    mut v___y_8649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_8651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329__overap_8652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_8651_ = l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___closed__0;
    v___x_1329__overap_8652_ = lean_panic_fn_borrowed(v___f_8651_, v_msg_8645_);
    leanh::lean_inc(v___y_8649_);
    leanh::lean_inc_ref(v___y_8648_);
    leanh::lean_inc(v___y_8647_);
    leanh::lean_inc_ref(v___y_8646_);
    v___x_8653_ = leanh::lean_apply_5(
        v___x_1329__overap_8652_,
        v___y_8646_,
        v___y_8647_,
        v___y_8648_,
        v___y_8649_,
        leanh::lean_box(0),
    );
    return v___x_8653_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___boxed(
    mut v_msg_8654_: *mut leanh::LeanObject,
    mut v___y_8655_: *mut leanh::LeanObject,
    mut v___y_8656_: *mut leanh::LeanObject,
    mut v___y_8657_: *mut leanh::LeanObject,
    mut v___y_8658_: *mut leanh::LeanObject,
    mut v___y_8659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8660_ = l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(
        v_msg_8654_,
        v___y_8655_,
        v___y_8656_,
        v___y_8657_,
        v___y_8658_,
    );
    leanh::lean_dec(v___y_8658_);
    leanh::lean_dec_ref(v___y_8657_);
    leanh::lean_dec(v___y_8656_);
    leanh::lean_dec_ref(v___y_8655_);
    return v_res_8660_;
}
pub unsafe fn _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_8661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8661_ = leanh::lean_box(0);
    v___x_8662_ = leanh::lean_unsigned_to_nat(16);
    v___x_8663_ = lean_mk_array(v___x_8662_, v___x_8661_);
    return v___x_8663_;
}
pub unsafe fn _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_8664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8664_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Closure_mkValueTypeClosure___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Closure_mkValueTypeClosure___closed__0_once),
        _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__0,
    );
    v___x_8665_ = leanh::lean_unsigned_to_nat(0);
    v___x_8666_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_8666_, 0, v___x_8665_);
    leanh::lean_ctor_set(v___x_8666_, 1, v___x_8664_);
    return v___x_8666_;
}
pub unsafe fn _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_8669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8669_ = leanh::lean_unsigned_to_nat(1);
    v___x_8670_ = l_Lean_Meta_Closure_mkValueTypeClosure___closed__2;
    v___x_8671_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Closure_mkValueTypeClosure___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Closure_mkValueTypeClosure___closed__1_once),
        _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1,
    );
    v___x_8672_ = leanh::lean_alloc_ctor(0, 12, (0) as u32);
    leanh::lean_ctor_set(v___x_8672_, 0, v___x_8671_);
    leanh::lean_ctor_set(v___x_8672_, 1, v___x_8671_);
    leanh::lean_ctor_set(v___x_8672_, 2, v___x_8670_);
    leanh::lean_ctor_set(v___x_8672_, 3, v___x_8669_);
    leanh::lean_ctor_set(v___x_8672_, 4, v___x_8670_);
    leanh::lean_ctor_set(v___x_8672_, 5, v___x_8670_);
    leanh::lean_ctor_set(v___x_8672_, 6, v___x_8670_);
    leanh::lean_ctor_set(v___x_8672_, 7, v___x_8670_);
    leanh::lean_ctor_set(v___x_8672_, 8, v___x_8669_);
    leanh::lean_ctor_set(v___x_8672_, 9, v___x_8670_);
    leanh::lean_ctor_set(v___x_8672_, 10, v___x_8670_);
    leanh::lean_ctor_set(v___x_8672_, 11, v___x_8670_);
    return v___x_8672_;
}
pub unsafe fn _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_8675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8675_ = l_Lean_Meta_Closure_mkValueTypeClosure___closed__5;
    v___x_8676_ = leanh::lean_unsigned_to_nat(2);
    v___x_8677_ = leanh::lean_unsigned_to_nat(417);
    v___x_8678_ = l_Lean_Meta_Closure_mkValueTypeClosure___closed__4;
    v___x_8679_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2;
    v___x_8680_ = l_mkPanicMessageWithDecl(
        v___x_8679_,
        v___x_8678_,
        v___x_8677_,
        v___x_8676_,
        v___x_8675_,
    );
    return v___x_8680_;
}
pub unsafe fn l_Lean_Meta_Closure_mkValueTypeClosure(
    mut v_type_8681_: *mut leanh::LeanObject,
    mut v_value_8682_: *mut leanh::LeanObject,
    mut v_zetaDelta_8683_: u8,
    mut v_a_8684_: *mut leanh::LeanObject,
    mut v_a_8685_: *mut leanh::LeanObject,
    mut v_a_8686_: *mut leanh::LeanObject,
    mut v_a_8687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_8694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_8696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelArgs_8697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDecls_8698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLocalDeclsForMVars_8699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLetDecls_8700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprMVarArgs_8701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprFVarArgs_8702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8709_: u8 = 0;
    let mut v_fst_8710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8717_: u8 = 0;
    let mut v___x_8718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8724_: u8 = 0;
    let mut v_a_8725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8728_: u8 = 0;
    let mut v___x_8730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8732_: u8 = 0;
    let mut v_a_8733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8736_: u8 = 0;
    let mut v___x_8738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8740_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8689_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Closure_mkValueTypeClosure___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Closure_mkValueTypeClosure___closed__3_once
                    ),
                    _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__3,
                );
                v___x_8690_ = lean_st_mk_ref(v___x_8689_);
                v___x_8691_ = l_Lean_Meta_Closure_mkValueTypeClosureAux(
                    v_type_8681_,
                    v_value_8682_,
                    v_zetaDelta_8683_,
                    v___x_8690_,
                    v_a_8684_,
                    v_a_8685_,
                    v_a_8686_,
                    v_a_8687_,
                );
                if leanh::lean_obj_tag(v___x_8691_) == 0 {
                    v_a_8692_ = leanh::lean_ctor_get(v___x_8691_, 0);
                    leanh::lean_inc(v_a_8692_);
                    leanh::lean_dec_ref_known(v___x_8691_, 1);
                    v___x_8693_ = lean_st_ref_get(v___x_8690_);
                    leanh::lean_dec(v___x_8690_);
                    v_fst_8694_ = leanh::lean_ctor_get(v_a_8692_, 0);
                    leanh::lean_inc(v_fst_8694_);
                    v_snd_8695_ = leanh::lean_ctor_get(v_a_8692_, 1);
                    leanh::lean_inc(v_snd_8695_);
                    leanh::lean_dec(v_a_8692_);
                    v_levelParams_8696_ = leanh::lean_ctor_get(v___x_8693_, 2);
                    leanh::lean_inc_ref(v_levelParams_8696_);
                    v_levelArgs_8697_ = leanh::lean_ctor_get(v___x_8693_, 4);
                    leanh::lean_inc_ref(v_levelArgs_8697_);
                    v_newLocalDecls_8698_ = leanh::lean_ctor_get(v___x_8693_, 5);
                    leanh::lean_inc_ref(v_newLocalDecls_8698_);
                    v_newLocalDeclsForMVars_8699_ = leanh::lean_ctor_get(v___x_8693_, 6);
                    leanh::lean_inc_ref(v_newLocalDeclsForMVars_8699_);
                    v_newLetDecls_8700_ = leanh::lean_ctor_get(v___x_8693_, 7);
                    leanh::lean_inc_ref(v_newLetDecls_8700_);
                    v_exprMVarArgs_8701_ = leanh::lean_ctor_get(v___x_8693_, 9);
                    leanh::lean_inc_ref(v_exprMVarArgs_8701_);
                    v_exprFVarArgs_8702_ = leanh::lean_ctor_get(v___x_8693_, 10);
                    leanh::lean_inc_ref(v_exprFVarArgs_8702_);
                    leanh::lean_dec(v___x_8693_);
                    v___x_8703_ = l_Array_reverse___redArg(v_newLocalDecls_8698_);
                    v___x_8704_ = l_Array_reverse___redArg(v_exprFVarArgs_8702_);
                    v___x_8705_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(
                        v___x_8703_,
                        v___x_8704_,
                        v_newLocalDeclsForMVars_8699_,
                        v_exprMVarArgs_8701_,
                        v_a_8686_,
                        v_a_8687_,
                    );
                    leanh::lean_dec_ref(v_newLocalDeclsForMVars_8699_);
                    if leanh::lean_obj_tag(v___x_8705_) == 0 {
                        v_a_8706_ = leanh::lean_ctor_get(v___x_8705_, 0);
                        v_isSharedCheck_8724_ =
                            (!leanh::lean_is_exclusive(v___x_8705_)) as u8;
                        if v_isSharedCheck_8724_ == 0 {
                            v___x_8708_ = v___x_8705_;
                            v_isShared_8709_ = v_isSharedCheck_8724_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_8706_);
                            leanh::lean_dec(v___x_8705_);
                            v___x_8708_ = leanh::lean_box(0);
                            v_isShared_8709_ = v_isSharedCheck_8724_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_newLetDecls_8700_);
                        leanh::lean_dec_ref(v_levelArgs_8697_);
                        leanh::lean_dec_ref(v_levelParams_8696_);
                        leanh::lean_dec(v_snd_8695_);
                        leanh::lean_dec(v_fst_8694_);
                        v_a_8725_ = leanh::lean_ctor_get(v___x_8705_, 0);
                        v_isSharedCheck_8732_ =
                            (!leanh::lean_is_exclusive(v___x_8705_)) as u8;
                        if v_isSharedCheck_8732_ == 0 {
                            v___x_8727_ = v___x_8705_;
                            v_isShared_8728_ = v_isSharedCheck_8732_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_8725_);
                            leanh::lean_dec(v___x_8705_);
                            v___x_8727_ = leanh::lean_box(0);
                            v_isShared_8728_ = v_isSharedCheck_8732_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_8690_);
                    v_a_8733_ = leanh::lean_ctor_get(v___x_8691_, 0);
                    v_isSharedCheck_8740_ = (!leanh::lean_is_exclusive(v___x_8691_)) as u8;
                    if v_isSharedCheck_8740_ == 0 {
                        v___x_8735_ = v___x_8691_;
                        v_isShared_8736_ = v_isSharedCheck_8740_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8733_);
                        leanh::lean_dec(v___x_8691_);
                        v___x_8735_ = leanh::lean_box(0);
                        v_isShared_8736_ = v_isSharedCheck_8740_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_8710_ = leanh::lean_ctor_get(v_a_8706_, 0);
                leanh::lean_inc_n(v_fst_8710_, 2);
                v_snd_8711_ = leanh::lean_ctor_get(v_a_8706_, 1);
                leanh::lean_inc(v_snd_8711_);
                leanh::lean_dec(v_a_8706_);
                v___x_8712_ = l_Array_reverse___redArg(v_newLetDecls_8700_);
                leanh::lean_inc_ref(v___x_8712_);
                v___x_8713_ = l_Lean_Meta_Closure_mkForall(v___x_8712_, v_fst_8694_);
                leanh::lean_dec(v_fst_8694_);
                v___x_8714_ = l_Lean_Meta_Closure_mkForall(v_fst_8710_, v___x_8713_);
                leanh::lean_dec_ref(v___x_8713_);
                v___x_8715_ = l_Lean_Meta_Closure_mkLambda(v___x_8712_, v_snd_8695_);
                leanh::lean_dec(v_snd_8695_);
                v___x_8716_ = l_Lean_Meta_Closure_mkLambda(v_fst_8710_, v___x_8715_);
                leanh::lean_dec_ref(v___x_8715_);
                v___x_8717_ = l_Lean_Expr_hasFVar(v___x_8716_);
                if v___x_8717_ == 0 {
                    v___x_8718_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_8718_, 0, v_levelParams_8696_);
                    leanh::lean_ctor_set(v___x_8718_, 1, v___x_8714_);
                    leanh::lean_ctor_set(v___x_8718_, 2, v___x_8716_);
                    leanh::lean_ctor_set(v___x_8718_, 3, v_levelArgs_8697_);
                    leanh::lean_ctor_set(v___x_8718_, 4, v_snd_8711_);
                    if v_isShared_8709_ == 0 {
                        leanh::lean_ctor_set(v___x_8708_, 0, v___x_8718_);
                        v___x_8720_ = v___x_8708_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8721_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8721_, 0, v___x_8718_);
                        v___x_8720_ = v_reuseFailAlloc_8721_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_8716_);
                    leanh::lean_dec_ref(v___x_8714_);
                    leanh::lean_dec(v_snd_8711_);
                    leanh::lean_del_object(v___x_8708_);
                    leanh::lean_dec_ref(v_levelArgs_8697_);
                    leanh::lean_dec_ref(v_levelParams_8696_);
                    v___x_8722_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Closure_mkValueTypeClosure___closed__6),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Closure_mkValueTypeClosure___closed__6_once
                        ),
                        _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__6,
                    );
                    v___x_8723_ = l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(
                        v___x_8722_,
                        v_a_8684_,
                        v_a_8685_,
                        v_a_8686_,
                        v_a_8687_,
                    );
                    return v___x_8723_;
                }
            }
            2 => {
                return v___x_8720_;
            }
            3 => {
                if v_isShared_8728_ == 0 {
                    v___x_8730_ = v___x_8727_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8731_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8731_, 0, v_a_8725_);
                    v___x_8730_ = v_reuseFailAlloc_8731_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8730_;
            }
            5 => {
                if v_isShared_8736_ == 0 {
                    v___x_8738_ = v___x_8735_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8739_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8739_, 0, v_a_8733_);
                    v___x_8738_ = v_reuseFailAlloc_8739_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8738_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Closure_mkValueTypeClosure___boxed(
    mut v_type_8741_: *mut leanh::LeanObject,
    mut v_value_8742_: *mut leanh::LeanObject,
    mut v_zetaDelta_8743_: *mut leanh::LeanObject,
    mut v_a_8744_: *mut leanh::LeanObject,
    mut v_a_8745_: *mut leanh::LeanObject,
    mut v_a_8746_: *mut leanh::LeanObject,
    mut v_a_8747_: *mut leanh::LeanObject,
    mut v_a_8748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zetaDelta_boxed_8749_: u8 = 0;
    let mut v_res_8750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_zetaDelta_boxed_8749_ = (leanh::lean_unbox(v_zetaDelta_8743_) as u8);
    v_res_8750_ = l_Lean_Meta_Closure_mkValueTypeClosure(
        v_type_8741_,
        v_value_8742_,
        v_zetaDelta_boxed_8749_,
        v_a_8744_,
        v_a_8745_,
        v_a_8746_,
        v_a_8747_,
    );
    leanh::lean_dec(v_a_8747_);
    leanh::lean_dec_ref(v_a_8746_);
    leanh::lean_dec(v_a_8745_);
    leanh::lean_dec_ref(v_a_8744_);
    return v_res_8750_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(
    mut v_name_8751_: *mut leanh::LeanObject,
    mut v_levelParams_8752_: *mut leanh::LeanObject,
    mut v_type_8753_: *mut leanh::LeanObject,
    mut v_value_8754_: *mut leanh::LeanObject,
    mut v_hints_8755_: *mut leanh::LeanObject,
    mut v___y_8756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8760_: u8 = 0;
    let mut v___x_8761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8767_: u8 = 0;
    let mut v___x_8768_: u8 = 0;
    let mut v___x_8769_: u8 = 0;
    let mut v_env_8770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8771_: u8 = 0;
    let mut v___x_8772_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8758_ = lean_st_ref_get(v___y_8756_);
                v_env_8770_ = leanh::lean_ctor_get(v___x_8758_, 0);
                leanh::lean_inc_ref_n(v_env_8770_, 2);
                leanh::lean_dec(v___x_8758_);
                v___x_8771_ = l_Lean_Environment_hasUnsafe(v_env_8770_, v_type_8753_);
                if v___x_8771_ == 0 {
                    v___x_8772_ = l_Lean_Environment_hasUnsafe(v_env_8770_, v_value_8754_);
                    v___y_8767_ = v___x_8772_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_env_8770_);
                    v___y_8767_ = v___x_8771_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_name_8751_);
                v___x_8761_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_8761_, 0, v_name_8751_);
                leanh::lean_ctor_set(v___x_8761_, 1, v_levelParams_8752_);
                leanh::lean_ctor_set(v___x_8761_, 2, v_type_8753_);
                v___x_8762_ = leanh::lean_box(0);
                v___x_8763_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8763_, 0, v_name_8751_);
                leanh::lean_ctor_set(v___x_8763_, 1, v___x_8762_);
                v___x_8764_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_8764_, 0, v___x_8761_);
                leanh::lean_ctor_set(v___x_8764_, 1, v_value_8754_);
                leanh::lean_ctor_set(v___x_8764_, 2, v_hints_8755_);
                leanh::lean_ctor_set(v___x_8764_, 3, v___x_8763_);
                leanh::lean_ctor_set_uint8(
                    v___x_8764_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___y_8760_,
                );
                v___x_8765_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_8765_, 0, v___x_8764_);
                return v___x_8765_;
            }
            2 => {
                if v___y_8767_ == 0 {
                    v___x_8768_ = 1;
                    v___y_8760_ = v___x_8768_;
                    state = 1;
                    continue;
                } else {
                    v___x_8769_ = 0;
                    v___y_8760_ = v___x_8769_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg___boxed(
    mut v_name_8773_: *mut leanh::LeanObject,
    mut v_levelParams_8774_: *mut leanh::LeanObject,
    mut v_type_8775_: *mut leanh::LeanObject,
    mut v_value_8776_: *mut leanh::LeanObject,
    mut v_hints_8777_: *mut leanh::LeanObject,
    mut v___y_8778_: *mut leanh::LeanObject,
    mut v___y_8779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8780_ =
        l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(
            v_name_8773_,
            v_levelParams_8774_,
            v_type_8775_,
            v_value_8776_,
            v_hints_8777_,
            v___y_8778_,
        );
    leanh::lean_dec(v___y_8778_);
    return v_res_8780_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0(
    mut v_name_8781_: *mut leanh::LeanObject,
    mut v_levelParams_8782_: *mut leanh::LeanObject,
    mut v_type_8783_: *mut leanh::LeanObject,
    mut v_value_8784_: *mut leanh::LeanObject,
    mut v_hints_8785_: *mut leanh::LeanObject,
    mut v___y_8786_: *mut leanh::LeanObject,
    mut v___y_8787_: *mut leanh::LeanObject,
    mut v___y_8788_: *mut leanh::LeanObject,
    mut v___y_8789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8791_ =
        l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(
            v_name_8781_,
            v_levelParams_8782_,
            v_type_8783_,
            v_value_8784_,
            v_hints_8785_,
            v___y_8789_,
        );
    return v___x_8791_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___boxed(
    mut v_name_8792_: *mut leanh::LeanObject,
    mut v_levelParams_8793_: *mut leanh::LeanObject,
    mut v_type_8794_: *mut leanh::LeanObject,
    mut v_value_8795_: *mut leanh::LeanObject,
    mut v_hints_8796_: *mut leanh::LeanObject,
    mut v___y_8797_: *mut leanh::LeanObject,
    mut v___y_8798_: *mut leanh::LeanObject,
    mut v___y_8799_: *mut leanh::LeanObject,
    mut v___y_8800_: *mut leanh::LeanObject,
    mut v___y_8801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8802_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0(
        v_name_8792_,
        v_levelParams_8793_,
        v_type_8794_,
        v_value_8795_,
        v_hints_8796_,
        v___y_8797_,
        v___y_8798_,
        v___y_8799_,
        v___y_8800_,
    );
    leanh::lean_dec(v___y_8800_);
    leanh::lean_dec_ref(v___y_8799_);
    leanh::lean_dec(v___y_8798_);
    leanh::lean_dec_ref(v___y_8797_);
    return v_res_8802_;
}
pub unsafe fn l_Lean_Meta_mkAuxDefinition(
    mut v_name_8803_: *mut leanh::LeanObject,
    mut v_type_8804_: *mut leanh::LeanObject,
    mut v_value_8805_: *mut leanh::LeanObject,
    mut v_zetaDelta_8806_: u8,
    mut v_compile_8807_: u8,
    mut v_logCompileErrors_8808_: u8,
    mut v_a_8809_: *mut leanh::LeanObject,
    mut v_a_8810_: *mut leanh::LeanObject,
    mut v_a_8811_: *mut leanh::LeanObject,
    mut v_a_8812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8818_: u8 = 0;
    let mut v___x_8819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_8820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_8821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_8822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_8823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelArgs_8824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprArgs_8825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8833_: u32 = 0;
    let mut v___x_8834_: u32 = 0;
    let mut v___x_8835_: u32 = 0;
    let mut v___x_8836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8842_: u8 = 0;
    let mut v___x_8844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8845_: u8 = 0;
    let mut v___x_8846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8851_: u8 = 0;
    let mut v___x_8853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8855_: u8 = 0;
    let mut v_a_8856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8859_: u8 = 0;
    let mut v___x_8861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8863_: u8 = 0;
    let mut v_reuseFailAlloc_8864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8865_: u8 = 0;
    let mut v_isSharedCheck_8866_: u8 = 0;
    let mut v_a_8867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8870_: u8 = 0;
    let mut v___x_8872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8874_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8814_ = l_Lean_Meta_Closure_mkValueTypeClosure(
                    v_type_8804_,
                    v_value_8805_,
                    v_zetaDelta_8806_,
                    v_a_8809_,
                    v_a_8810_,
                    v_a_8811_,
                    v_a_8812_,
                );
                if leanh::lean_obj_tag(v___x_8814_) == 0 {
                    v_a_8815_ = leanh::lean_ctor_get(v___x_8814_, 0);
                    v_isSharedCheck_8866_ = (!leanh::lean_is_exclusive(v___x_8814_)) as u8;
                    if v_isSharedCheck_8866_ == 0 {
                        v___x_8817_ = v___x_8814_;
                        v_isShared_8818_ = v_isSharedCheck_8866_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8815_);
                        leanh::lean_dec(v___x_8814_);
                        v___x_8817_ = leanh::lean_box(0);
                        v_isShared_8818_ = v_isSharedCheck_8866_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_name_8803_);
                    v_a_8867_ = leanh::lean_ctor_get(v___x_8814_, 0);
                    v_isSharedCheck_8874_ = (!leanh::lean_is_exclusive(v___x_8814_)) as u8;
                    if v_isSharedCheck_8874_ == 0 {
                        v___x_8869_ = v___x_8814_;
                        v_isShared_8870_ = v_isSharedCheck_8874_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8867_);
                        leanh::lean_dec(v___x_8814_);
                        v___x_8869_ = leanh::lean_box(0);
                        v_isShared_8870_ = v_isSharedCheck_8874_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8819_ = lean_st_ref_get(v_a_8812_);
                v_env_8820_ = leanh::lean_ctor_get(v___x_8819_, 0);
                leanh::lean_inc_ref(v_env_8820_);
                leanh::lean_dec(v___x_8819_);
                v_levelParams_8821_ = leanh::lean_ctor_get(v_a_8815_, 0);
                leanh::lean_inc_ref(v_levelParams_8821_);
                v_type_8822_ = leanh::lean_ctor_get(v_a_8815_, 1);
                leanh::lean_inc_ref(v_type_8822_);
                v_value_8823_ = leanh::lean_ctor_get(v_a_8815_, 2);
                leanh::lean_inc_ref_n(v_value_8823_, 2);
                v_levelArgs_8824_ = leanh::lean_ctor_get(v_a_8815_, 3);
                leanh::lean_inc_ref(v_levelArgs_8824_);
                v_exprArgs_8825_ = leanh::lean_ctor_get(v_a_8815_, 4);
                leanh::lean_inc_ref(v_exprArgs_8825_);
                leanh::lean_dec(v_a_8815_);
                v___x_8833_ = l_Lean_getMaxHeight(v_env_8820_, v_value_8823_);
                v___x_8834_ = 1;
                v___x_8835_ = lean_uint32_add(v___x_8833_, v___x_8834_);
                v___x_8836_ = leanh::lean_alloc_ctor(2, 0, (4) as u32);
                leanh::lean_ctor_set_uint32(v___x_8836_, 0 as u32, v___x_8835_);
                v___x_8837_ = lean_array_to_list(v_levelParams_8821_);
                leanh::lean_inc(v_name_8803_);
                v___x_8838_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_8803_, v___x_8837_, v_type_8822_, v_value_8823_, v___x_8836_, v_a_8812_);
                v_a_8839_ = leanh::lean_ctor_get(v___x_8838_, 0);
                v_isSharedCheck_8865_ = (!leanh::lean_is_exclusive(v___x_8838_)) as u8;
                if v_isSharedCheck_8865_ == 0 {
                    v___x_8841_ = v___x_8838_;
                    v_isShared_8842_ = v_isSharedCheck_8865_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_a_8839_);
                    leanh::lean_dec(v___x_8838_);
                    v___x_8841_ = leanh::lean_box(0);
                    v_isShared_8842_ = v_isSharedCheck_8865_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_8827_ = lean_array_to_list(v_levelArgs_8824_);
                v___x_8828_ = l_Lean_mkConst(v_name_8803_, v___x_8827_);
                v___x_8829_ = l_Lean_mkAppN(v___x_8828_, v_exprArgs_8825_);
                leanh::lean_dec_ref(v_exprArgs_8825_);
                if v_isShared_8818_ == 0 {
                    leanh::lean_ctor_set(v___x_8817_, 0, v___x_8829_);
                    v___x_8831_ = v___x_8817_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8832_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8832_, 0, v___x_8829_);
                    v___x_8831_ = v_reuseFailAlloc_8832_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_8831_;
            }
            4 => {
                if v_isShared_8842_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_8841_, 1);
                    v___x_8844_ = v___x_8841_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8864_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8864_, 0, v_a_8839_);
                    v___x_8844_ = v_reuseFailAlloc_8864_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_8845_ = 0;
                leanh::lean_inc_ref(v___x_8844_);
                v___x_8846_ = l_Lean_addDecl(v___x_8844_, v___x_8845_, v_a_8811_, v_a_8812_);
                if leanh::lean_obj_tag(v___x_8846_) == 0 {
                    leanh::lean_dec_ref_known(v___x_8846_, 1);
                    if v_compile_8807_ == 0 {
                        leanh::lean_dec_ref(v___x_8844_);
                        state = 2;
                        continue;
                    } else {
                        v___x_8847_ = l_Lean_compileDecl(
                            v___x_8844_,
                            v_logCompileErrors_8808_,
                            v_a_8811_,
                            v_a_8812_,
                        );
                        if leanh::lean_obj_tag(v___x_8847_) == 0 {
                            leanh::lean_dec_ref_known(v___x_8847_, 1);
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_exprArgs_8825_);
                            leanh::lean_dec_ref(v_levelArgs_8824_);
                            leanh::lean_del_object(v___x_8817_);
                            leanh::lean_dec(v_name_8803_);
                            v_a_8848_ = leanh::lean_ctor_get(v___x_8847_, 0);
                            v_isSharedCheck_8855_ =
                                (!leanh::lean_is_exclusive(v___x_8847_)) as u8;
                            if v_isSharedCheck_8855_ == 0 {
                                v___x_8850_ = v___x_8847_;
                                v_isShared_8851_ = v_isSharedCheck_8855_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_8848_);
                                leanh::lean_dec(v___x_8847_);
                                v___x_8850_ = leanh::lean_box(0);
                                v_isShared_8851_ = v_isSharedCheck_8855_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_8844_);
                    leanh::lean_dec_ref(v_exprArgs_8825_);
                    leanh::lean_dec_ref(v_levelArgs_8824_);
                    leanh::lean_del_object(v___x_8817_);
                    leanh::lean_dec(v_name_8803_);
                    v_a_8856_ = leanh::lean_ctor_get(v___x_8846_, 0);
                    v_isSharedCheck_8863_ = (!leanh::lean_is_exclusive(v___x_8846_)) as u8;
                    if v_isSharedCheck_8863_ == 0 {
                        v___x_8858_ = v___x_8846_;
                        v_isShared_8859_ = v_isSharedCheck_8863_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8856_);
                        leanh::lean_dec(v___x_8846_);
                        v___x_8858_ = leanh::lean_box(0);
                        v_isShared_8859_ = v_isSharedCheck_8863_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_8851_ == 0 {
                    v___x_8853_ = v___x_8850_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8854_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8854_, 0, v_a_8848_);
                    v___x_8853_ = v_reuseFailAlloc_8854_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_8853_;
            }
            8 => {
                if v_isShared_8859_ == 0 {
                    v___x_8861_ = v___x_8858_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8862_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8862_, 0, v_a_8856_);
                    v___x_8861_ = v_reuseFailAlloc_8862_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_8861_;
            }
            10 => {
                if v_isShared_8870_ == 0 {
                    v___x_8872_ = v___x_8869_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_8873_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8873_, 0, v_a_8867_);
                    v___x_8872_ = v_reuseFailAlloc_8873_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_8872_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkAuxDefinition___boxed(
    mut v_name_8875_: *mut leanh::LeanObject,
    mut v_type_8876_: *mut leanh::LeanObject,
    mut v_value_8877_: *mut leanh::LeanObject,
    mut v_zetaDelta_8878_: *mut leanh::LeanObject,
    mut v_compile_8879_: *mut leanh::LeanObject,
    mut v_logCompileErrors_8880_: *mut leanh::LeanObject,
    mut v_a_8881_: *mut leanh::LeanObject,
    mut v_a_8882_: *mut leanh::LeanObject,
    mut v_a_8883_: *mut leanh::LeanObject,
    mut v_a_8884_: *mut leanh::LeanObject,
    mut v_a_8885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zetaDelta_boxed_8886_: u8 = 0;
    let mut v_compile_boxed_8887_: u8 = 0;
    let mut v_logCompileErrors_boxed_8888_: u8 = 0;
    let mut v_res_8889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_zetaDelta_boxed_8886_ = (leanh::lean_unbox(v_zetaDelta_8878_) as u8);
    v_compile_boxed_8887_ = (leanh::lean_unbox(v_compile_8879_) as u8);
    v_logCompileErrors_boxed_8888_ = (leanh::lean_unbox(v_logCompileErrors_8880_) as u8);
    v_res_8889_ = l_Lean_Meta_mkAuxDefinition(
        v_name_8875_,
        v_type_8876_,
        v_value_8877_,
        v_zetaDelta_boxed_8886_,
        v_compile_boxed_8887_,
        v_logCompileErrors_boxed_8888_,
        v_a_8881_,
        v_a_8882_,
        v_a_8883_,
        v_a_8884_,
    );
    leanh::lean_dec(v_a_8884_);
    leanh::lean_dec_ref(v_a_8883_);
    leanh::lean_dec(v_a_8882_);
    leanh::lean_dec_ref(v_a_8881_);
    return v_res_8889_;
}
pub unsafe fn l_Lean_Meta_mkAuxDefinitionFor(
    mut v_name_8890_: *mut leanh::LeanObject,
    mut v_value_8891_: *mut leanh::LeanObject,
    mut v_zetaDelta_8892_: u8,
    mut v_compile_8893_: u8,
    mut v_logCompileErrors_8894_: u8,
    mut v_a_8895_: *mut leanh::LeanObject,
    mut v_a_8896_: *mut leanh::LeanObject,
    mut v_a_8897_: *mut leanh::LeanObject,
    mut v_a_8898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8900_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_8898_);
    leanh::lean_inc_ref(v_a_8897_);
    leanh::lean_inc(v_a_8896_);
    leanh::lean_inc_ref(v_a_8895_);
    leanh::lean_inc_ref(v_value_8891_);
    v___x_8900_ = lean_infer_type(v_value_8891_, v_a_8895_, v_a_8896_, v_a_8897_, v_a_8898_);
    if leanh::lean_obj_tag(v___x_8900_) == 0 {
        let mut v_a_8901_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8902_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8903_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_8901_ = leanh::lean_ctor_get(v___x_8900_, 0);
        leanh::lean_inc(v_a_8901_);
        leanh::lean_dec_ref_known(v___x_8900_, 1);
        v___x_8902_ = l_Lean_Expr_headBeta(v_a_8901_);
        v___x_8903_ = l_Lean_Meta_mkAuxDefinition(
            v_name_8890_,
            v___x_8902_,
            v_value_8891_,
            v_zetaDelta_8892_,
            v_compile_8893_,
            v_logCompileErrors_8894_,
            v_a_8895_,
            v_a_8896_,
            v_a_8897_,
            v_a_8898_,
        );
        return v___x_8903_;
    } else {
        leanh::lean_dec_ref(v_value_8891_);
        leanh::lean_dec(v_name_8890_);
        return v___x_8900_;
    }
}
pub unsafe fn l_Lean_Meta_mkAuxDefinitionFor___boxed(
    mut v_name_8904_: *mut leanh::LeanObject,
    mut v_value_8905_: *mut leanh::LeanObject,
    mut v_zetaDelta_8906_: *mut leanh::LeanObject,
    mut v_compile_8907_: *mut leanh::LeanObject,
    mut v_logCompileErrors_8908_: *mut leanh::LeanObject,
    mut v_a_8909_: *mut leanh::LeanObject,
    mut v_a_8910_: *mut leanh::LeanObject,
    mut v_a_8911_: *mut leanh::LeanObject,
    mut v_a_8912_: *mut leanh::LeanObject,
    mut v_a_8913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zetaDelta_boxed_8914_: u8 = 0;
    let mut v_compile_boxed_8915_: u8 = 0;
    let mut v_logCompileErrors_boxed_8916_: u8 = 0;
    let mut v_res_8917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_zetaDelta_boxed_8914_ = (leanh::lean_unbox(v_zetaDelta_8906_) as u8);
    v_compile_boxed_8915_ = (leanh::lean_unbox(v_compile_8907_) as u8);
    v_logCompileErrors_boxed_8916_ = (leanh::lean_unbox(v_logCompileErrors_8908_) as u8);
    v_res_8917_ = l_Lean_Meta_mkAuxDefinitionFor(
        v_name_8904_,
        v_value_8905_,
        v_zetaDelta_boxed_8914_,
        v_compile_boxed_8915_,
        v_logCompileErrors_boxed_8916_,
        v_a_8909_,
        v_a_8910_,
        v_a_8911_,
        v_a_8912_,
    );
    leanh::lean_dec(v_a_8912_);
    leanh::lean_dec_ref(v_a_8911_);
    leanh::lean_dec(v_a_8910_);
    leanh::lean_dec_ref(v_a_8909_);
    return v_res_8917_;
}
pub unsafe fn l_Lean_Meta_mkAuxTheorem(
    mut v_type_8918_: *mut leanh::LeanObject,
    mut v_value_8919_: *mut leanh::LeanObject,
    mut v_zetaDelta_8920_: u8,
    mut v_kind_x3f_8921_: *mut leanh::LeanObject,
    mut v_cache_8922_: u8,
    mut v_a_8923_: *mut leanh::LeanObject,
    mut v_a_8924_: *mut leanh::LeanObject,
    mut v_a_8925_: *mut leanh::LeanObject,
    mut v_a_8926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_8930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_8931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_8932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelArgs_8933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprArgs_8934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8936_: u8 = 0;
    let mut v___x_8937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8941_: u8 = 0;
    let mut v___x_8942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8948_: u8 = 0;
    let mut v_a_8949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8952_: u8 = 0;
    let mut v___x_8954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8956_: u8 = 0;
    let mut v_a_8957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8960_: u8 = 0;
    let mut v___x_8962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8964_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8928_ = l_Lean_Meta_Closure_mkValueTypeClosure(
                    v_type_8918_,
                    v_value_8919_,
                    v_zetaDelta_8920_,
                    v_a_8923_,
                    v_a_8924_,
                    v_a_8925_,
                    v_a_8926_,
                );
                if leanh::lean_obj_tag(v___x_8928_) == 0 {
                    v_a_8929_ = leanh::lean_ctor_get(v___x_8928_, 0);
                    leanh::lean_inc(v_a_8929_);
                    leanh::lean_dec_ref_known(v___x_8928_, 1);
                    v_levelParams_8930_ = leanh::lean_ctor_get(v_a_8929_, 0);
                    leanh::lean_inc_ref(v_levelParams_8930_);
                    v_type_8931_ = leanh::lean_ctor_get(v_a_8929_, 1);
                    leanh::lean_inc_ref(v_type_8931_);
                    v_value_8932_ = leanh::lean_ctor_get(v_a_8929_, 2);
                    leanh::lean_inc_ref(v_value_8932_);
                    v_levelArgs_8933_ = leanh::lean_ctor_get(v_a_8929_, 3);
                    leanh::lean_inc_ref(v_levelArgs_8933_);
                    v_exprArgs_8934_ = leanh::lean_ctor_get(v_a_8929_, 4);
                    leanh::lean_inc_ref(v_exprArgs_8934_);
                    leanh::lean_dec(v_a_8929_);
                    v___x_8935_ = lean_array_to_list(v_levelParams_8930_);
                    v___x_8936_ = 0;
                    v___x_8937_ = l_Lean_Meta_mkAuxLemma(
                        v___x_8935_,
                        v_type_8931_,
                        v_value_8932_,
                        v_kind_x3f_8921_,
                        v_cache_8922_,
                        v___x_8936_,
                        v___x_8936_,
                        v___x_8936_,
                        v_a_8923_,
                        v_a_8924_,
                        v_a_8925_,
                        v_a_8926_,
                    );
                    if leanh::lean_obj_tag(v___x_8937_) == 0 {
                        v_a_8938_ = leanh::lean_ctor_get(v___x_8937_, 0);
                        v_isSharedCheck_8948_ =
                            (!leanh::lean_is_exclusive(v___x_8937_)) as u8;
                        if v_isSharedCheck_8948_ == 0 {
                            v___x_8940_ = v___x_8937_;
                            v_isShared_8941_ = v_isSharedCheck_8948_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_8938_);
                            leanh::lean_dec(v___x_8937_);
                            v___x_8940_ = leanh::lean_box(0);
                            v_isShared_8941_ = v_isSharedCheck_8948_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_exprArgs_8934_);
                        leanh::lean_dec_ref(v_levelArgs_8933_);
                        v_a_8949_ = leanh::lean_ctor_get(v___x_8937_, 0);
                        v_isSharedCheck_8956_ =
                            (!leanh::lean_is_exclusive(v___x_8937_)) as u8;
                        if v_isSharedCheck_8956_ == 0 {
                            v___x_8951_ = v___x_8937_;
                            v_isShared_8952_ = v_isSharedCheck_8956_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_8949_);
                            leanh::lean_dec(v___x_8937_);
                            v___x_8951_ = leanh::lean_box(0);
                            v_isShared_8952_ = v_isSharedCheck_8956_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_kind_x3f_8921_);
                    v_a_8957_ = leanh::lean_ctor_get(v___x_8928_, 0);
                    v_isSharedCheck_8964_ = (!leanh::lean_is_exclusive(v___x_8928_)) as u8;
                    if v_isSharedCheck_8964_ == 0 {
                        v___x_8959_ = v___x_8928_;
                        v_isShared_8960_ = v_isSharedCheck_8964_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8957_);
                        leanh::lean_dec(v___x_8928_);
                        v___x_8959_ = leanh::lean_box(0);
                        v_isShared_8960_ = v_isSharedCheck_8964_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8942_ = lean_array_to_list(v_levelArgs_8933_);
                v___x_8943_ = l_Lean_mkConst(v_a_8938_, v___x_8942_);
                v___x_8944_ = l_Lean_mkAppN(v___x_8943_, v_exprArgs_8934_);
                leanh::lean_dec_ref(v_exprArgs_8934_);
                if v_isShared_8941_ == 0 {
                    leanh::lean_ctor_set(v___x_8940_, 0, v___x_8944_);
                    v___x_8946_ = v___x_8940_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8947_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8947_, 0, v___x_8944_);
                    v___x_8946_ = v_reuseFailAlloc_8947_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8946_;
            }
            3 => {
                if v_isShared_8952_ == 0 {
                    v___x_8954_ = v___x_8951_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8955_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8955_, 0, v_a_8949_);
                    v___x_8954_ = v_reuseFailAlloc_8955_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8954_;
            }
            5 => {
                if v_isShared_8960_ == 0 {
                    v___x_8962_ = v___x_8959_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8963_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8963_, 0, v_a_8957_);
                    v___x_8962_ = v_reuseFailAlloc_8963_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8962_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkAuxTheorem___boxed(
    mut v_type_8965_: *mut leanh::LeanObject,
    mut v_value_8966_: *mut leanh::LeanObject,
    mut v_zetaDelta_8967_: *mut leanh::LeanObject,
    mut v_kind_x3f_8968_: *mut leanh::LeanObject,
    mut v_cache_8969_: *mut leanh::LeanObject,
    mut v_a_8970_: *mut leanh::LeanObject,
    mut v_a_8971_: *mut leanh::LeanObject,
    mut v_a_8972_: *mut leanh::LeanObject,
    mut v_a_8973_: *mut leanh::LeanObject,
    mut v_a_8974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zetaDelta_boxed_8975_: u8 = 0;
    let mut v_cache_boxed_8976_: u8 = 0;
    let mut v_res_8977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_zetaDelta_boxed_8975_ = (leanh::lean_unbox(v_zetaDelta_8967_) as u8);
    v_cache_boxed_8976_ = (leanh::lean_unbox(v_cache_8969_) as u8);
    v_res_8977_ = l_Lean_Meta_mkAuxTheorem(
        v_type_8965_,
        v_value_8966_,
        v_zetaDelta_boxed_8975_,
        v_kind_x3f_8968_,
        v_cache_boxed_8976_,
        v_a_8970_,
        v_a_8971_,
        v_a_8972_,
        v_a_8973_,
    );
    leanh::lean_dec(v_a_8973_);
    leanh::lean_dec_ref(v_a_8972_);
    leanh::lean_dec(v_a_8971_);
    leanh::lean_dec_ref(v_a_8970_);
    return v_res_8977_;
}
pub unsafe fn l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_9033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9034_: u8 = 0;
    let mut v___x_9035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9036_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9033_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10;
    v___x_9034_ = 0;
    v___x_9035_ = l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_;
    v___x_9036_ = l_Lean_registerTraceClass(v___x_9033_, v___x_9034_, v___x_9035_);
    return v___x_9036_;
}
pub unsafe fn l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2____boxed(
    mut v_a_9037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9038_ = l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_();
    return v_res_9038_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Closure(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Check(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_AuxLemma(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ForEachExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Closure(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Closure(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Check(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_AuxLemma(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_ForEachExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Closure(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Closure(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Closure(builtin);
}
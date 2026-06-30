// Lean compiler output
// Module: Lean.Meta.Transform
// Imports: Lean.Meta.FunInfo Init.Data.Range.Polymorphic.Iterators
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_size,
    lean_array_push, lean_array_set, lean_array_size, lean_array_uget_borrowed, lean_array_uset,
    lean_expr_instantiate_rev, lean_mk_array, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_nat_sub, lean_nat_to_int, lean_ptr_addr, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor,
    lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat,
    lean_usize_sub,
};
use crate::r#gen::Init::Control::Basic::{
    l_instMonadControlTOfMonadControl___redArg___lam__3,
    l_instMonadControlTOfMonadControl___redArg___lam__4,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map;
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Prelude::l_Lean_maxRecDepthErrorMessage;
use crate::r#gen::Init::System::CancelToken::l_IO_CancelToken_isSet;
use crate::r#gen::Init::System::ST::{
    l_ST_Prim_Ref_get___boxed, l_ST_Prim_Ref_modifyGetUnsafe___boxed, l_ST_Prim_mkRef___boxed,
};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_checkSystem, l_Lean_Core_checkSystem___boxed,
    l_Lean_Core_instantiateValueLevelParams, l_Lean_Core_liftIOCore___boxed,
    l_Lean_Core_withIncRecDepth___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_hasValue;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f, l_Lean_Environment_setExporting,
    l_Lean_Environment_unlockAsync,
};
use crate::r#gen::Lean::Exception::l_Lean_interruptExceptionId;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_beta, l_Lean_Expr_betaRev,
    l_Lean_Expr_const___override, l_Lean_Expr_constLevels_x21, l_Lean_Expr_constName_x21,
    l_Lean_Expr_forallE___override, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_hasMVar, l_Lean_Expr_headBeta, l_Lean_Expr_isConst, l_Lean_Expr_isHeadBetaTarget,
    l_Lean_Expr_lam___override, l_Lean_Expr_letE___override, l_Lean_Expr_mdata___override,
    l_Lean_Expr_proj___override, l_Lean_Expr_sort___override, l_Lean_Expr_withAppAux___redArg,
    l_Lean_ExprStructEq_beq, l_Lean_ExprStructEq_beq___boxed, l_Lean_ExprStructEq_hash,
    l_Lean_ExprStructEq_hash___boxed, l_Lean_inaccessible_x3f, l_Lean_instBEqBinderInfo_beq,
    l_Lean_instBEqFVarId_beq, l_Lean_instReprExpr_repr, l_Lean_mkAppN, l_Lean_patternWithRef_x3f,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_index, l_Lean_LocalDecl_value_x3f, lean_local_ctx_num_indices,
};
use crate::r#gen::Lean::Message::l_Lean_MessageData_ofFormat;
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp, l_Lean_FVarId_findDecl_x3f___redArg,
    l_Lean_FVarId_getValue_x3f___redArg, l_Lean_Meta_mkForallFVars,
    l_Lean_Meta_mkForallFVars___boxed, l_Lean_Meta_mkLambdaFVars,
    l_Lean_Meta_mkLambdaFVars___boxed, l_Lean_Meta_mkLetFVars, l_Lean_Meta_mkLetFVars___boxed,
    l_Lean_Meta_withIncRecDepth___redArg, l_Lean_Meta_withLetDecl___redArg,
    l_Lean_Meta_withLocalDecl___redArg,
};
use crate::r#gen::Lean::Meta::FunInfo::{
    initialize_Lean_Meta_FunInfo, l_Lean_Meta_getFunInfoNArgs, l_Lean_Meta_getFunInfoNArgs___boxed,
    runtime_initialize_Lean_Meta_FunInfo,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::MonadCache::{
    l_Lean_MonadCacheT_instMonad___aux__13___boxed, l_Lean_MonadCacheT_instMonad___redArg,
    l_Lean_MonadCacheT_instMonadControl___redArg,
    l_Lean_MonadCacheT_instMonadLift___aux__1___boxed,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insert___redArg,
};
pub static l_Lean_instInhabitedTransformStep_default___closed__0_value:
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
        95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0,
    ],
};
static mut l_Lean_instInhabitedTransformStep_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedTransformStep_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instInhabitedTransformStep_default___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_instInhabitedTransformStep_default___closed__0_value)
            as *mut leanh::LeanObject,
        17542774118954891045 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instInhabitedTransformStep_default___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedTransformStep_default___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instInhabitedTransformStep_default___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedTransformStep_default___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instInhabitedTransformStep_default___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedTransformStep_default___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedTransformStep_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedTransformStep: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__0_value:
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
    m_data: [110, 111, 110, 101, 0],
};
static mut l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__2_value:
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
    m_data: [115, 111, 109, 101, 32, 0],
};
static mut l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__3_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__2_value
    ) as *mut leanh::LeanObject],
};
static mut l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_instReprTransformStep_repr___closed__0_value: leanh::LeanStringObject<24> =
    leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 84, 114, 97, 110, 115, 102, 111, 114, 109, 83, 116, 101, 112, 46,
            100, 111, 110, 101, 0,
        ],
    };
static mut l_Lean_instReprTransformStep_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprTransformStep_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprTransformStep_repr___closed__1_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprTransformStep_repr___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprTransformStep_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprTransformStep_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprTransformStep_repr___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprTransformStep_repr___closed__1_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprTransformStep_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprTransformStep_repr___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instReprTransformStep_repr___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprTransformStep_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instReprTransformStep_repr___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprTransformStep_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprTransformStep_repr___closed__5_value: leanh::LeanStringObject<25> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            76, 101, 97, 110, 46, 84, 114, 97, 110, 115, 102, 111, 114, 109, 83, 116, 101, 112, 46,
            118, 105, 115, 105, 116, 0,
        ],
    };
static mut l_Lean_instReprTransformStep_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprTransformStep_repr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprTransformStep_repr___closed__6_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprTransformStep_repr___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprTransformStep_repr___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprTransformStep_repr___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprTransformStep_repr___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprTransformStep_repr___closed__6_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprTransformStep_repr___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprTransformStep_repr___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprTransformStep_repr___closed__8_value: leanh::LeanStringObject<28> =
    leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 84, 114, 97, 110, 115, 102, 111, 114, 109, 83, 116, 101, 112, 46,
            99, 111, 110, 116, 105, 110, 117, 101, 0,
        ],
    };
static mut l_Lean_instReprTransformStep_repr___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprTransformStep_repr___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprTransformStep_repr___closed__9_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprTransformStep_repr___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprTransformStep_repr___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprTransformStep_repr___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprTransformStep_repr___closed__10_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprTransformStep_repr___closed__9_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprTransformStep_repr___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprTransformStep_repr___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprTransformStep___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprTransformStep_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprTransformStep___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprTransformStep___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instReprTransformStep: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprTransformStep___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 114, 97, 110, 115, 102, 111, 114, 109, 0]};
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__1_value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_checkSystem___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_ExprStructEq_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_ExprStructEq_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Core_transform___redArg___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Core_transform___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Core_transform___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Core_transform___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Core_transform___redArg___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Core_transform___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Core_betaReduce___lam__0___closed__0_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 2,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lean_Core_betaReduce___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Core_betaReduce___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value) as *mut leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value) as *mut leanh::LeanObject,7310567555909517314 as *mut leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value) as *mut leanh::LeanObject,273128857561458264 as *mut leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Core_betaReduce___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Core_betaReduce___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Core_betaReduce___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Core_betaReduce___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Core_betaReduce___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Core_betaReduce___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Core_betaReduce___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Core_betaReduce___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___closed__0_value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_zetaReduce___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_zetaReduce___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_zetaReduce___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_zetaReduce___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_eraseInaccessibleAnnotations___closed__0_value:
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
    m_fun: l_Lean_Meta_eraseInaccessibleAnnotations___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_eraseInaccessibleAnnotations___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_eraseInaccessibleAnnotations___closed__1_value:
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
    m_fun: l_Lean_Meta_eraseInaccessibleAnnotations___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_eraseInaccessibleAnnotations___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_eraseInaccessibleAnnotations___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_erasePatternRefAnnotations___closed__0_value:
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
    m_fun: l_Lean_Meta_erasePatternRefAnnotations___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_erasePatternRefAnnotations___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_erasePatternRefAnnotations___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_TransformStep_ctorIdx(
    mut v_x_5517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_5517_) {
        0 => {
            let mut v___x_5518_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_5518_ = leanh::lean_unsigned_to_nat(0);
            return v___x_5518_;
        }
        1 => {
            let mut v___x_5519_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_5519_ = leanh::lean_unsigned_to_nat(1);
            return v___x_5519_;
        }
        _ => {
            let mut v___x_5520_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_5520_ = leanh::lean_unsigned_to_nat(2);
            return v___x_5520_;
        }
    }
}
pub unsafe fn l_Lean_TransformStep_ctorIdx___boxed(
    mut v_x_5521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5522_ = l_Lean_TransformStep_ctorIdx(v_x_5521_);
    leanh::lean_dec_ref(v_x_5521_);
    return v_res_5522_;
}
pub unsafe fn l_Lean_TransformStep_ctorElim___redArg(
    mut v_t_5523_: *mut leanh::LeanObject,
    mut v_k_5524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_5523_) == 2 {
        let mut v_e_x3f_5525_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5526_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_e_x3f_5525_ = leanh::lean_ctor_get(v_t_5523_, 0);
        leanh::lean_inc(v_e_x3f_5525_);
        leanh::lean_dec_ref_known(v_t_5523_, 1);
        v___x_5526_ = leanh::lean_apply_1(v_k_5524_, v_e_x3f_5525_);
        return v___x_5526_;
    } else {
        let mut v_e_5527_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5528_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_e_5527_ = leanh::lean_ctor_get(v_t_5523_, 0);
        leanh::lean_inc_ref(v_e_5527_);
        leanh::lean_dec_ref(v_t_5523_);
        v___x_5528_ = leanh::lean_apply_1(v_k_5524_, v_e_5527_);
        return v___x_5528_;
    }
}
pub unsafe fn l_Lean_TransformStep_ctorElim(
    mut v_motive_5529_: *mut leanh::LeanObject,
    mut v_ctorIdx_5530_: *mut leanh::LeanObject,
    mut v_t_5531_: *mut leanh::LeanObject,
    mut v_h_5532_: *mut leanh::LeanObject,
    mut v_k_5533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5534_ = l_Lean_TransformStep_ctorElim___redArg(v_t_5531_, v_k_5533_);
    return v___x_5534_;
}
pub unsafe fn l_Lean_TransformStep_ctorElim___boxed(
    mut v_motive_5535_: *mut leanh::LeanObject,
    mut v_ctorIdx_5536_: *mut leanh::LeanObject,
    mut v_t_5537_: *mut leanh::LeanObject,
    mut v_h_5538_: *mut leanh::LeanObject,
    mut v_k_5539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5540_ = l_Lean_TransformStep_ctorElim(
        v_motive_5535_,
        v_ctorIdx_5536_,
        v_t_5537_,
        v_h_5538_,
        v_k_5539_,
    );
    leanh::lean_dec(v_ctorIdx_5536_);
    return v_res_5540_;
}
pub unsafe fn l_Lean_TransformStep_done_elim___redArg(
    mut v_t_5541_: *mut leanh::LeanObject,
    mut v_done_5542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5543_ = l_Lean_TransformStep_ctorElim___redArg(v_t_5541_, v_done_5542_);
    return v___x_5543_;
}
pub unsafe fn l_Lean_TransformStep_done_elim(
    mut v_motive_5544_: *mut leanh::LeanObject,
    mut v_t_5545_: *mut leanh::LeanObject,
    mut v_h_5546_: *mut leanh::LeanObject,
    mut v_done_5547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5548_ = l_Lean_TransformStep_ctorElim___redArg(v_t_5545_, v_done_5547_);
    return v___x_5548_;
}
pub unsafe fn l_Lean_TransformStep_visit_elim___redArg(
    mut v_t_5549_: *mut leanh::LeanObject,
    mut v_visit_5550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5551_ = l_Lean_TransformStep_ctorElim___redArg(v_t_5549_, v_visit_5550_);
    return v___x_5551_;
}
pub unsafe fn l_Lean_TransformStep_visit_elim(
    mut v_motive_5552_: *mut leanh::LeanObject,
    mut v_t_5553_: *mut leanh::LeanObject,
    mut v_h_5554_: *mut leanh::LeanObject,
    mut v_visit_5555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5556_ = l_Lean_TransformStep_ctorElim___redArg(v_t_5553_, v_visit_5555_);
    return v___x_5556_;
}
pub unsafe fn l_Lean_TransformStep_continue_elim___redArg(
    mut v_t_5557_: *mut leanh::LeanObject,
    mut v_continue_5558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5559_ = l_Lean_TransformStep_ctorElim___redArg(v_t_5557_, v_continue_5558_);
    return v___x_5559_;
}
pub unsafe fn l_Lean_TransformStep_continue_elim(
    mut v_motive_5560_: *mut leanh::LeanObject,
    mut v_t_5561_: *mut leanh::LeanObject,
    mut v_h_5562_: *mut leanh::LeanObject,
    mut v_continue_5563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5564_ = l_Lean_TransformStep_ctorElim___redArg(v_t_5561_, v_continue_5563_);
    return v___x_5564_;
}
pub unsafe fn _init_l_Lean_instInhabitedTransformStep_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5568_ = leanh::lean_box(0);
    v___x_5569_ = l_Lean_instInhabitedTransformStep_default___closed__1;
    v___x_5570_ = l_Lean_Expr_const___override(v___x_5569_, v___x_5568_);
    return v___x_5570_;
}
pub unsafe fn _init_l_Lean_instInhabitedTransformStep_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5571_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedTransformStep_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedTransformStep_default___closed__2_once),
        _init_l_Lean_instInhabitedTransformStep_default___closed__2,
    );
    v___x_5572_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5572_, 0, v___x_5571_);
    return v___x_5572_;
}
pub unsafe fn _init_l_Lean_instInhabitedTransformStep_default() -> *mut leanh::LeanObject {
    let mut v___x_5573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5573_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedTransformStep_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedTransformStep_default___closed__3_once),
        _init_l_Lean_instInhabitedTransformStep_default___closed__3,
    );
    return v___x_5573_;
}
pub unsafe fn _init_l_Lean_instInhabitedTransformStep() -> *mut leanh::LeanObject {
    let mut v___x_5574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5574_ = l_Lean_instInhabitedTransformStep_default;
    return v___x_5574_;
}
pub unsafe fn l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0(
    mut v_x_5581_: *mut leanh::LeanObject,
    mut v_x_5582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_5581_) == 0 {
        let mut v___x_5583_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5583_ = l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__1;
        return v___x_5583_;
    } else {
        let mut v_val_5584_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5585_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5586_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5587_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5588_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5589_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5584_ = leanh::lean_ctor_get(v_x_5581_, 0);
        leanh::lean_inc(v_val_5584_);
        leanh::lean_dec_ref_known(v_x_5581_, 1);
        v___x_5585_ = l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__3;
        v___x_5586_ = leanh::lean_unsigned_to_nat(1024);
        v___x_5587_ = l_Lean_instReprExpr_repr(v_val_5584_, v___x_5586_);
        v___x_5588_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5588_, 0, v___x_5585_);
        leanh::lean_ctor_set(v___x_5588_, 1, v___x_5587_);
        v___x_5589_ = l_Repr_addAppParen(v___x_5588_, v_x_5582_);
        return v___x_5589_;
    }
}
pub unsafe fn l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___boxed(
    mut v_x_5590_: *mut leanh::LeanObject,
    mut v_x_5591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5592_ =
        l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0(v_x_5590_, v_x_5591_);
    leanh::lean_dec(v_x_5591_);
    return v_res_5592_;
}
pub unsafe fn _init_l_Lean_instReprTransformStep_repr___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_5599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5599_ = leanh::lean_unsigned_to_nat(2);
    v___x_5600_ = lean_nat_to_int(v___x_5599_);
    return v___x_5600_;
}
pub unsafe fn _init_l_Lean_instReprTransformStep_repr___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_5601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5601_ = leanh::lean_unsigned_to_nat(1);
    v___x_5602_ = lean_nat_to_int(v___x_5601_);
    return v___x_5602_;
}
pub unsafe fn l_Lean_instReprTransformStep_repr(
    mut v_x_5615_: *mut leanh::LeanObject,
    mut v_prec_5616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_e_5617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: u8 = 0;
    let mut v___x_5626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: u8 = 0;
    let mut v___x_5630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_5632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5640_: u8 = 0;
    let mut v___x_5641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: u8 = 0;
    let mut v___x_5645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_5647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5655_: u8 = 0;
    let mut v___x_5656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: u8 = 0;
    let mut v___x_5660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_5615_) {
                0 => {
                    v_e_5617_ = leanh::lean_ctor_get(v_x_5615_, 0);
                    leanh::lean_inc_ref(v_e_5617_);
                    leanh::lean_dec_ref_known(v_x_5615_, 1);
                    v___x_5628_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_5629_ = lean_nat_dec_le(v___x_5628_, v_prec_5616_);
                    if v___x_5629_ == 0 {
                        v___x_5630_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprTransformStep_repr___closed__3),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprTransformStep_repr___closed__3_once
                            ),
                            _init_l_Lean_instReprTransformStep_repr___closed__3,
                        );
                        v___y_5619_ = v___x_5630_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5631_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprTransformStep_repr___closed__4),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprTransformStep_repr___closed__4_once
                            ),
                            _init_l_Lean_instReprTransformStep_repr___closed__4,
                        );
                        v___y_5619_ = v___x_5631_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_e_5632_ = leanh::lean_ctor_get(v_x_5615_, 0);
                    leanh::lean_inc_ref(v_e_5632_);
                    leanh::lean_dec_ref_known(v_x_5615_, 1);
                    v___x_5643_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_5644_ = lean_nat_dec_le(v___x_5643_, v_prec_5616_);
                    if v___x_5644_ == 0 {
                        v___x_5645_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprTransformStep_repr___closed__3),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprTransformStep_repr___closed__3_once
                            ),
                            _init_l_Lean_instReprTransformStep_repr___closed__3,
                        );
                        v___y_5634_ = v___x_5645_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5646_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprTransformStep_repr___closed__4),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprTransformStep_repr___closed__4_once
                            ),
                            _init_l_Lean_instReprTransformStep_repr___closed__4,
                        );
                        v___y_5634_ = v___x_5646_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v_e_x3f_5647_ = leanh::lean_ctor_get(v_x_5615_, 0);
                    leanh::lean_inc(v_e_x3f_5647_);
                    leanh::lean_dec_ref_known(v_x_5615_, 1);
                    v___x_5658_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_5659_ = lean_nat_dec_le(v___x_5658_, v_prec_5616_);
                    if v___x_5659_ == 0 {
                        v___x_5660_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprTransformStep_repr___closed__3),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprTransformStep_repr___closed__3_once
                            ),
                            _init_l_Lean_instReprTransformStep_repr___closed__3,
                        );
                        v___y_5649_ = v___x_5660_;
                        state = 3;
                        continue;
                    } else {
                        v___x_5661_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprTransformStep_repr___closed__4),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprTransformStep_repr___closed__4_once
                            ),
                            _init_l_Lean_instReprTransformStep_repr___closed__4,
                        );
                        v___y_5649_ = v___x_5661_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_5620_ = l_Lean_instReprTransformStep_repr___closed__2;
                v___x_5621_ = leanh::lean_unsigned_to_nat(1024);
                v___x_5622_ = l_Lean_instReprExpr_repr(v_e_5617_, v___x_5621_);
                v___x_5623_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5623_, 0, v___x_5620_);
                leanh::lean_ctor_set(v___x_5623_, 1, v___x_5622_);
                leanh::lean_inc(v___y_5619_);
                v___x_5624_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5624_, 0, v___y_5619_);
                leanh::lean_ctor_set(v___x_5624_, 1, v___x_5623_);
                v___x_5625_ = 0;
                v___x_5626_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_5626_, 0, v___x_5624_);
                leanh::lean_ctor_set_uint8(
                    v___x_5626_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_5625_,
                );
                v___x_5627_ = l_Repr_addAppParen(v___x_5626_, v_prec_5616_);
                return v___x_5627_;
            }
            2 => {
                v___x_5635_ = l_Lean_instReprTransformStep_repr___closed__7;
                v___x_5636_ = leanh::lean_unsigned_to_nat(1024);
                v___x_5637_ = l_Lean_instReprExpr_repr(v_e_5632_, v___x_5636_);
                v___x_5638_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5638_, 0, v___x_5635_);
                leanh::lean_ctor_set(v___x_5638_, 1, v___x_5637_);
                leanh::lean_inc(v___y_5634_);
                v___x_5639_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5639_, 0, v___y_5634_);
                leanh::lean_ctor_set(v___x_5639_, 1, v___x_5638_);
                v___x_5640_ = 0;
                v___x_5641_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_5641_, 0, v___x_5639_);
                leanh::lean_ctor_set_uint8(
                    v___x_5641_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_5640_,
                );
                v___x_5642_ = l_Repr_addAppParen(v___x_5641_, v_prec_5616_);
                return v___x_5642_;
            }
            3 => {
                v___x_5650_ = l_Lean_instReprTransformStep_repr___closed__10;
                v___x_5651_ = leanh::lean_unsigned_to_nat(1024);
                v___x_5652_ = l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0(
                    v_e_x3f_5647_,
                    v___x_5651_,
                );
                v___x_5653_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5653_, 0, v___x_5650_);
                leanh::lean_ctor_set(v___x_5653_, 1, v___x_5652_);
                leanh::lean_inc(v___y_5649_);
                v___x_5654_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5654_, 0, v___y_5649_);
                leanh::lean_ctor_set(v___x_5654_, 1, v___x_5653_);
                v___x_5655_ = 0;
                v___x_5656_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_5656_, 0, v___x_5654_);
                leanh::lean_ctor_set_uint8(
                    v___x_5656_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_5655_,
                );
                v___x_5657_ = l_Repr_addAppParen(v___x_5656_, v_prec_5616_);
                return v___x_5657_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instReprTransformStep_repr___boxed(
    mut v_x_5662_: *mut leanh::LeanObject,
    mut v_prec_5663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5664_ = l_Lean_instReprTransformStep_repr(v_x_5662_, v_prec_5663_);
    leanh::lean_dec(v_prec_5663_);
    return v_res_5664_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__0(
    mut v_toApplicative_5667_: *mut leanh::LeanObject,
    mut v_a_5668_: *mut leanh::LeanObject,
    mut v_a_5669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toPure_5670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toPure_5670_ = leanh::lean_ctor_get(v_toApplicative_5667_, 1);
    leanh::lean_inc(v_toPure_5670_);
    leanh::lean_dec_ref(v_toApplicative_5667_);
    v___x_5671_ = leanh::lean_apply_2(v_toPure_5670_, leanh::lean_box(0), v_a_5668_);
    return v___x_5671_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__1(
    mut v___x_5672_: *mut leanh::LeanObject,
    mut v___x_5673_: *mut leanh::LeanObject,
    mut v_e_5674_: *mut leanh::LeanObject,
    mut v_a_5675_: *mut leanh::LeanObject,
    mut v_s_5676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5677_ = leanh::lean_box(0);
    v___x_5678_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v___x_5672_,
        v___x_5673_,
        v_s_5676_,
        v_e_5674_,
        v_a_5675_,
    );
    v___x_5679_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5679_, 0, v___x_5677_);
    leanh::lean_ctor_set(v___x_5679_, 1, v___x_5678_);
    return v___x_5679_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2(
    mut v_toApplicative_5680_: *mut leanh::LeanObject,
    mut v___x_5681_: *mut leanh::LeanObject,
    mut v___x_5682_: *mut leanh::LeanObject,
    mut v_e_5683_: *mut leanh::LeanObject,
    mut v_a_5684_: *mut leanh::LeanObject,
    mut v_x_5685_: *mut leanh::LeanObject,
    mut v_toBind_5686_: *mut leanh::LeanObject,
    mut v_a_5687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_a_5687_);
    v___f_5688_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_5688_, 0, v_toApplicative_5680_);
    leanh::lean_closure_set(v___f_5688_, 1, v_a_5687_);
    v___f_5689_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__1
            as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_5689_, 0, v___x_5681_);
    leanh::lean_closure_set(v___f_5689_, 1, v___x_5682_);
    leanh::lean_closure_set(v___f_5689_, 2, v_e_5683_);
    leanh::lean_closure_set(v___f_5689_, 3, v_a_5687_);
    leanh::lean_inc(v_a_5684_);
    v___x_5690_ = leanh::lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___x_5690_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_5690_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_5690_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_5690_, 3, v_a_5684_);
    leanh::lean_closure_set(v___x_5690_, 4, v___f_5689_);
    v___x_5691_ = leanh::lean_apply_2(v_x_5685_, leanh::lean_box(0), v___x_5690_);
    v___x_5692_ = leanh::lean_apply_4(
        v_toBind_5686_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5691_,
        v___f_5688_,
    );
    return v___x_5692_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2___boxed(
    mut v_toApplicative_5693_: *mut leanh::LeanObject,
    mut v___x_5694_: *mut leanh::LeanObject,
    mut v___x_5695_: *mut leanh::LeanObject,
    mut v_e_5696_: *mut leanh::LeanObject,
    mut v_a_5697_: *mut leanh::LeanObject,
    mut v_x_5698_: *mut leanh::LeanObject,
    mut v_toBind_5699_: *mut leanh::LeanObject,
    mut v_a_5700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5701_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2(
        v_toApplicative_5693_,
        v___x_5694_,
        v___x_5695_,
        v_e_5696_,
        v_a_5697_,
        v_x_5698_,
        v_toBind_5699_,
        v_a_5700_,
    );
    leanh::lean_dec(v_a_5697_);
    return v_res_5701_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3(
    mut v_toApplicative_5702_: *mut leanh::LeanObject,
    mut v___x_5703_: *mut leanh::LeanObject,
    mut v___x_5704_: *mut leanh::LeanObject,
    mut v_e_5705_: *mut leanh::LeanObject,
    mut v_a_5706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toPure_5707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toPure_5707_ = leanh::lean_ctor_get(v_toApplicative_5702_, 1);
    leanh::lean_inc(v_toPure_5707_);
    leanh::lean_dec_ref(v_toApplicative_5702_);
    v___x_5708_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v___x_5703_,
        v___x_5704_,
        v_a_5706_,
        v_e_5705_,
    );
    v___x_5709_ =
        leanh::lean_apply_2(v_toPure_5707_, leanh::lean_box(0), v___x_5708_);
    return v___x_5709_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed(
    mut v_toApplicative_5710_: *mut leanh::LeanObject,
    mut v___x_5711_: *mut leanh::LeanObject,
    mut v___x_5712_: *mut leanh::LeanObject,
    mut v_e_5713_: *mut leanh::LeanObject,
    mut v_a_5714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5715_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3(
        v_toApplicative_5710_,
        v___x_5711_,
        v___x_5712_,
        v_e_5713_,
        v_a_5714_,
    );
    leanh::lean_dec_ref(v_a_5714_);
    return v_res_5715_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19(
    mut v_inst_5719_: *mut leanh::LeanObject,
    mut v_x_5720_: *mut leanh::LeanObject,
    mut v___x_5721_: *mut leanh::LeanObject,
    mut v___x_5722_: *mut leanh::LeanObject,
    mut v_inst_5723_: *mut leanh::LeanObject,
    mut v___f_5724_: *mut leanh::LeanObject,
    mut v___x_5725_: *mut leanh::LeanObject,
    mut v___x_5726_: *mut leanh::LeanObject,
    mut v_a_5727_: *mut leanh::LeanObject,
    mut v_toBind_5728_: *mut leanh::LeanObject,
    mut v___f_5729_: *mut leanh::LeanObject,
    mut v_toApplicative_5730_: *mut leanh::LeanObject,
    mut v_a_5731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_a_5731_) == 0 {
        let mut v___x_5732_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5733_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5734_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5735_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2445__overap_5736_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5737_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5738_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_toApplicative_5730_);
        v___x_5732_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__1;
        v___x_5733_ =
            leanh::lean_apply_2(v_inst_5719_, leanh::lean_box(0), v___x_5732_);
        leanh::lean_inc_ref(v___x_5722_);
        leanh::lean_inc_ref(v___x_5721_);
        v___x_5734_ = leanh::lean_alloc_closure(
            l_Lean_MonadCacheT_instMonadLift___aux__1___boxed as *mut core::ffi::c_void,
            10,
            9,
        );
        leanh::lean_closure_set(v___x_5734_, 0, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_5734_, 1, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_5734_, 2, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_5734_, 3, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_5734_, 4, v_x_5720_);
        leanh::lean_closure_set(v___x_5734_, 5, v___x_5721_);
        leanh::lean_closure_set(v___x_5734_, 6, v___x_5722_);
        leanh::lean_closure_set(v___x_5734_, 7, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_5734_, 8, v___x_5733_);
        v___x_5735_ = leanh::lean_alloc_closure(
            l_Lean_MonadCacheT_instMonad___aux__13___boxed as *mut core::ffi::c_void,
            13,
            12,
        );
        leanh::lean_closure_set(v___x_5735_, 0, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_5735_, 1, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_5735_, 2, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_5735_, 3, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_5735_, 4, v_x_5720_);
        leanh::lean_closure_set(v___x_5735_, 5, v___x_5721_);
        leanh::lean_closure_set(v___x_5735_, 6, v___x_5722_);
        leanh::lean_closure_set(v___x_5735_, 7, v_inst_5723_);
        leanh::lean_closure_set(v___x_5735_, 8, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_5735_, 9, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_5735_, 10, v___x_5734_);
        leanh::lean_closure_set(v___x_5735_, 11, v___f_5724_);
        v___x_2445__overap_5736_ =
            l_Lean_Core_withIncRecDepth___redArg(v___x_5725_, v___x_5726_, v___x_5735_);
        leanh::lean_inc(v_a_5727_);
        v___x_5737_ = leanh::lean_apply_1(v___x_2445__overap_5736_, v_a_5727_);
        v___x_5738_ = leanh::lean_apply_4(
            v_toBind_5728_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_5737_,
            v___f_5729_,
        );
        return v___x_5738_;
    } else {
        let mut v_val_5739_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_5740_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5741_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_5729_);
        leanh::lean_dec(v_toBind_5728_);
        leanh::lean_dec_ref(v___x_5726_);
        leanh::lean_dec_ref(v___x_5725_);
        leanh::lean_dec(v___f_5724_);
        leanh::lean_dec_ref(v_inst_5723_);
        leanh::lean_dec_ref(v___x_5722_);
        leanh::lean_dec_ref(v___x_5721_);
        leanh::lean_dec(v_inst_5719_);
        v_val_5739_ = leanh::lean_ctor_get(v_a_5731_, 0);
        leanh::lean_inc(v_val_5739_);
        leanh::lean_dec_ref_known(v_a_5731_, 1);
        v_toPure_5740_ = leanh::lean_ctor_get(v_toApplicative_5730_, 1);
        leanh::lean_inc(v_toPure_5740_);
        leanh::lean_dec_ref(v_toApplicative_5730_);
        v___x_5741_ =
            leanh::lean_apply_2(v_toPure_5740_, leanh::lean_box(0), v_val_5739_);
        return v___x_5741_;
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___boxed(
    mut v_inst_5742_: *mut leanh::LeanObject,
    mut v_x_5743_: *mut leanh::LeanObject,
    mut v___x_5744_: *mut leanh::LeanObject,
    mut v___x_5745_: *mut leanh::LeanObject,
    mut v_inst_5746_: *mut leanh::LeanObject,
    mut v___f_5747_: *mut leanh::LeanObject,
    mut v___x_5748_: *mut leanh::LeanObject,
    mut v___x_5749_: *mut leanh::LeanObject,
    mut v_a_5750_: *mut leanh::LeanObject,
    mut v_toBind_5751_: *mut leanh::LeanObject,
    mut v___f_5752_: *mut leanh::LeanObject,
    mut v_toApplicative_5753_: *mut leanh::LeanObject,
    mut v_a_5754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5755_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19(
        v_inst_5742_,
        v_x_5743_,
        v___x_5744_,
        v___x_5745_,
        v_inst_5746_,
        v___f_5747_,
        v___x_5748_,
        v___x_5749_,
        v_a_5750_,
        v_toBind_5751_,
        v___f_5752_,
        v_toApplicative_5753_,
        v_a_5754_,
    );
    leanh::lean_dec(v_a_5750_);
    return v_res_5755_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4(
    mut v_a_5758_: *mut leanh::LeanObject,
    mut v_inst_5759_: *mut leanh::LeanObject,
    mut v_inst_5760_: *mut leanh::LeanObject,
    mut v_inst_5761_: *mut leanh::LeanObject,
    mut v_pre_5762_: *mut leanh::LeanObject,
    mut v_post_5763_: *mut leanh::LeanObject,
    mut v_x_5764_: *mut leanh::LeanObject,
    mut v_x_5765_: *mut leanh::LeanObject,
    mut v___y_5766_: *mut leanh::LeanObject,
    mut v_a_5767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5768_ = l_Lean_mkAppN(v_a_5758_, v_a_5767_);
    v___x_5769_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(
        v_inst_5759_,
        v_inst_5760_,
        v_inst_5761_,
        v_pre_5762_,
        v_post_5763_,
        v_x_5764_,
        v_x_5765_,
        v___x_5768_,
        v___y_5766_,
    );
    return v___x_5769_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4___boxed(
    mut v_a_5770_: *mut leanh::LeanObject,
    mut v_inst_5771_: *mut leanh::LeanObject,
    mut v_inst_5772_: *mut leanh::LeanObject,
    mut v_inst_5773_: *mut leanh::LeanObject,
    mut v_pre_5774_: *mut leanh::LeanObject,
    mut v_post_5775_: *mut leanh::LeanObject,
    mut v_x_5776_: *mut leanh::LeanObject,
    mut v_x_5777_: *mut leanh::LeanObject,
    mut v___y_5778_: *mut leanh::LeanObject,
    mut v_a_5779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5780_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4(
        v_a_5770_,
        v_inst_5771_,
        v_inst_5772_,
        v_inst_5773_,
        v_pre_5774_,
        v_post_5775_,
        v_x_5776_,
        v_x_5777_,
        v___y_5778_,
        v_a_5779_,
    );
    leanh::lean_dec_ref(v_a_5779_);
    leanh::lean_dec(v___y_5778_);
    return v_res_5780_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___boxed(
    mut v_inst_5781_: *mut leanh::LeanObject,
    mut v_inst_5782_: *mut leanh::LeanObject,
    mut v_inst_5783_: *mut leanh::LeanObject,
    mut v_pre_5784_: *mut leanh::LeanObject,
    mut v_post_5785_: *mut leanh::LeanObject,
    mut v_x_5786_: *mut leanh::LeanObject,
    mut v_x_5787_: *mut leanh::LeanObject,
    mut v_e_5788_: *mut leanh::LeanObject,
    mut v_a_5789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5790_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(
        v_inst_5781_,
        v_inst_5782_,
        v_inst_5783_,
        v_pre_5784_,
        v_post_5785_,
        v_x_5786_,
        v_x_5787_,
        v_e_5788_,
        v_a_5789_,
    );
    leanh::lean_dec(v_a_5789_);
    return v_res_5790_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5(
    mut v_inst_5791_: *mut leanh::LeanObject,
    mut v_inst_5792_: *mut leanh::LeanObject,
    mut v_inst_5793_: *mut leanh::LeanObject,
    mut v_pre_5794_: *mut leanh::LeanObject,
    mut v_post_5795_: *mut leanh::LeanObject,
    mut v_x_5796_: *mut leanh::LeanObject,
    mut v_x_5797_: *mut leanh::LeanObject,
    mut v___y_5798_: *mut leanh::LeanObject,
    mut v_args_5799_: *mut leanh::LeanObject,
    mut v___x_5800_: *mut leanh::LeanObject,
    mut v_toBind_5801_: *mut leanh::LeanObject,
    mut v_a_5802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5805_: usize = 0;
    let mut v___x_5806_: usize = 0;
    let mut v___x_2175__overap_5807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_n(v___y_5798_, 2);
    leanh::lean_inc(v_x_5797_);
    leanh::lean_inc(v_post_5795_);
    leanh::lean_inc(v_pre_5794_);
    leanh::lean_inc_ref(v_inst_5793_);
    leanh::lean_inc(v_inst_5792_);
    leanh::lean_inc_ref(v_inst_5791_);
    v___f_5803_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4___boxed
            as *mut core::ffi::c_void,
        10,
        9,
    );
    leanh::lean_closure_set(v___f_5803_, 0, v_a_5802_);
    leanh::lean_closure_set(v___f_5803_, 1, v_inst_5791_);
    leanh::lean_closure_set(v___f_5803_, 2, v_inst_5792_);
    leanh::lean_closure_set(v___f_5803_, 3, v_inst_5793_);
    leanh::lean_closure_set(v___f_5803_, 4, v_pre_5794_);
    leanh::lean_closure_set(v___f_5803_, 5, v_post_5795_);
    leanh::lean_closure_set(v___f_5803_, 6, v_x_5796_);
    leanh::lean_closure_set(v___f_5803_, 7, v_x_5797_);
    leanh::lean_closure_set(v___f_5803_, 8, v___y_5798_);
    v___x_5804_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___boxed
            as *mut core::ffi::c_void,
        9,
        7,
    );
    leanh::lean_closure_set(v___x_5804_, 0, v_inst_5791_);
    leanh::lean_closure_set(v___x_5804_, 1, v_inst_5792_);
    leanh::lean_closure_set(v___x_5804_, 2, v_inst_5793_);
    leanh::lean_closure_set(v___x_5804_, 3, v_pre_5794_);
    leanh::lean_closure_set(v___x_5804_, 4, v_post_5795_);
    leanh::lean_closure_set(v___x_5804_, 5, v_x_5796_);
    leanh::lean_closure_set(v___x_5804_, 6, v_x_5797_);
    v_sz_5805_ = lean_array_size(v_args_5799_);
    v___x_5806_ = 0usize;
    v___x_2175__overap_5807_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5800_,
        v___x_5804_,
        v_sz_5805_,
        v___x_5806_,
        v_args_5799_,
    );
    v___x_5808_ = leanh::lean_apply_1(v___x_2175__overap_5807_, v___y_5798_);
    v___x_5809_ = leanh::lean_apply_4(
        v_toBind_5801_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5808_,
        v___f_5803_,
    );
    return v___x_5809_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5___boxed(
    mut v_inst_5810_: *mut leanh::LeanObject,
    mut v_inst_5811_: *mut leanh::LeanObject,
    mut v_inst_5812_: *mut leanh::LeanObject,
    mut v_pre_5813_: *mut leanh::LeanObject,
    mut v_post_5814_: *mut leanh::LeanObject,
    mut v_x_5815_: *mut leanh::LeanObject,
    mut v_x_5816_: *mut leanh::LeanObject,
    mut v___y_5817_: *mut leanh::LeanObject,
    mut v_args_5818_: *mut leanh::LeanObject,
    mut v___x_5819_: *mut leanh::LeanObject,
    mut v_toBind_5820_: *mut leanh::LeanObject,
    mut v_a_5821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5822_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5(
        v_inst_5810_,
        v_inst_5811_,
        v_inst_5812_,
        v_pre_5813_,
        v_post_5814_,
        v_x_5815_,
        v_x_5816_,
        v___y_5817_,
        v_args_5818_,
        v___x_5819_,
        v_toBind_5820_,
        v_a_5821_,
    );
    leanh::lean_dec(v___y_5817_);
    return v_res_5822_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6(
    mut v_inst_5823_: *mut leanh::LeanObject,
    mut v_inst_5824_: *mut leanh::LeanObject,
    mut v_inst_5825_: *mut leanh::LeanObject,
    mut v_pre_5826_: *mut leanh::LeanObject,
    mut v_post_5827_: *mut leanh::LeanObject,
    mut v_x_5828_: *mut leanh::LeanObject,
    mut v_x_5829_: *mut leanh::LeanObject,
    mut v___x_5830_: *mut leanh::LeanObject,
    mut v_toBind_5831_: *mut leanh::LeanObject,
    mut v_f_5832_: *mut leanh::LeanObject,
    mut v_args_5833_: *mut leanh::LeanObject,
    mut v___y_5834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_5831_);
    leanh::lean_inc(v___y_5834_);
    leanh::lean_inc(v_x_5829_);
    leanh::lean_inc(v_post_5827_);
    leanh::lean_inc(v_pre_5826_);
    leanh::lean_inc_ref(v_inst_5825_);
    leanh::lean_inc(v_inst_5824_);
    leanh::lean_inc_ref(v_inst_5823_);
    v___f_5835_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5___boxed
            as *mut core::ffi::c_void,
        12,
        11,
    );
    leanh::lean_closure_set(v___f_5835_, 0, v_inst_5823_);
    leanh::lean_closure_set(v___f_5835_, 1, v_inst_5824_);
    leanh::lean_closure_set(v___f_5835_, 2, v_inst_5825_);
    leanh::lean_closure_set(v___f_5835_, 3, v_pre_5826_);
    leanh::lean_closure_set(v___f_5835_, 4, v_post_5827_);
    leanh::lean_closure_set(v___f_5835_, 5, v_x_5828_);
    leanh::lean_closure_set(v___f_5835_, 6, v_x_5829_);
    leanh::lean_closure_set(v___f_5835_, 7, v___y_5834_);
    leanh::lean_closure_set(v___f_5835_, 8, v_args_5833_);
    leanh::lean_closure_set(v___f_5835_, 9, v___x_5830_);
    leanh::lean_closure_set(v___f_5835_, 10, v_toBind_5831_);
    v___x_5836_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(
        v_inst_5823_,
        v_inst_5824_,
        v_inst_5825_,
        v_pre_5826_,
        v_post_5827_,
        v_x_5828_,
        v_x_5829_,
        v_f_5832_,
        v___y_5834_,
    );
    v___x_5837_ = leanh::lean_apply_4(
        v_toBind_5831_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5836_,
        v___f_5835_,
    );
    return v___x_5837_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6___boxed(
    mut v_inst_5838_: *mut leanh::LeanObject,
    mut v_inst_5839_: *mut leanh::LeanObject,
    mut v_inst_5840_: *mut leanh::LeanObject,
    mut v_pre_5841_: *mut leanh::LeanObject,
    mut v_post_5842_: *mut leanh::LeanObject,
    mut v_x_5843_: *mut leanh::LeanObject,
    mut v_x_5844_: *mut leanh::LeanObject,
    mut v___x_5845_: *mut leanh::LeanObject,
    mut v_toBind_5846_: *mut leanh::LeanObject,
    mut v_f_5847_: *mut leanh::LeanObject,
    mut v_args_5848_: *mut leanh::LeanObject,
    mut v___y_5849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5850_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6(
        v_inst_5838_,
        v_inst_5839_,
        v_inst_5840_,
        v_pre_5841_,
        v_post_5842_,
        v_x_5843_,
        v_x_5844_,
        v___x_5845_,
        v_toBind_5846_,
        v_f_5847_,
        v_args_5848_,
        v___y_5849_,
    );
    leanh::lean_dec(v___y_5849_);
    return v_res_5850_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7___boxed(
    mut v_inst_5851_: *mut leanh::LeanObject,
    mut v_inst_5852_: *mut leanh::LeanObject,
    mut v_inst_5853_: *mut leanh::LeanObject,
    mut v_pre_5854_: *mut leanh::LeanObject,
    mut v_post_5855_: *mut leanh::LeanObject,
    mut v_x_5856_: *mut leanh::LeanObject,
    mut v_x_5857_: *mut leanh::LeanObject,
    mut v___y_5858_: *mut leanh::LeanObject,
    mut v_a_5859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5860_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7(
        v_inst_5851_,
        v_inst_5852_,
        v_inst_5853_,
        v_pre_5854_,
        v_post_5855_,
        v_x_5856_,
        v_x_5857_,
        v___y_5858_,
        v_a_5859_,
    );
    leanh::lean_dec(v___y_5858_);
    return v_res_5860_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8(
    mut v_binderName_5861_: *mut leanh::LeanObject,
    mut v_a_5862_: *mut leanh::LeanObject,
    mut v_binderInfo_5863_: u8,
    mut v_inst_5864_: *mut leanh::LeanObject,
    mut v_inst_5865_: *mut leanh::LeanObject,
    mut v_inst_5866_: *mut leanh::LeanObject,
    mut v_pre_5867_: *mut leanh::LeanObject,
    mut v_post_5868_: *mut leanh::LeanObject,
    mut v_x_5869_: *mut leanh::LeanObject,
    mut v_x_5870_: *mut leanh::LeanObject,
    mut v___y_5871_: *mut leanh::LeanObject,
    mut v___y_5872_: *mut leanh::LeanObject,
    mut v_binderType_5873_: *mut leanh::LeanObject,
    mut v_body_5874_: *mut leanh::LeanObject,
    mut v_a_5875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5877_: u8 = 0;
    let mut v___x_5878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: u8 = 0;
    let mut v___x_5881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5884_: usize = 0;
    let mut v___x_5885_: usize = 0;
    let mut v___x_5886_: u8 = 0;
    let mut v___x_5887_: usize = 0;
    let mut v___x_5888_: usize = 0;
    let mut v___x_5889_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5884_ = lean_ptr_addr(v_binderType_5873_);
                v___x_5885_ = lean_ptr_addr(v_a_5862_);
                v___x_5886_ = lean_usize_dec_eq(v___x_5884_, v___x_5885_);
                if v___x_5886_ == 0 {
                    v___y_5877_ = v___x_5886_;
                    state = 1;
                    continue;
                } else {
                    v___x_5887_ = lean_ptr_addr(v_body_5874_);
                    v___x_5888_ = lean_ptr_addr(v_a_5875_);
                    v___x_5889_ = lean_usize_dec_eq(v___x_5887_, v___x_5888_);
                    v___y_5877_ = v___x_5889_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_5877_ == 0 {
                    leanh::lean_dec_ref(v___y_5872_);
                    v___x_5878_ = l_Lean_Expr_forallE___override(
                        v_binderName_5861_,
                        v_a_5862_,
                        v_a_5875_,
                        v_binderInfo_5863_,
                    );
                    v___x_5879_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_5864_, v_inst_5865_, v_inst_5866_, v_pre_5867_, v_post_5868_, v_x_5869_, v_x_5870_, v___x_5878_, v___y_5871_);
                    return v___x_5879_;
                } else {
                    v___x_5880_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_5863_, v_binderInfo_5863_);
                    if v___x_5880_ == 0 {
                        leanh::lean_dec_ref(v___y_5872_);
                        v___x_5881_ = l_Lean_Expr_forallE___override(
                            v_binderName_5861_,
                            v_a_5862_,
                            v_a_5875_,
                            v_binderInfo_5863_,
                        );
                        v___x_5882_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_5864_, v_inst_5865_, v_inst_5866_, v_pre_5867_, v_post_5868_, v_x_5869_, v_x_5870_, v___x_5881_, v___y_5871_);
                        return v___x_5882_;
                    } else {
                        leanh::lean_dec_ref(v_a_5875_);
                        leanh::lean_dec_ref(v_a_5862_);
                        leanh::lean_dec(v_binderName_5861_);
                        v___x_5883_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_5864_, v_inst_5865_, v_inst_5866_, v_pre_5867_, v_post_5868_, v_x_5869_, v_x_5870_, v___y_5872_, v___y_5871_);
                        return v___x_5883_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8___boxed(
    mut v_binderName_5890_: *mut leanh::LeanObject,
    mut v_a_5891_: *mut leanh::LeanObject,
    mut v_binderInfo_5892_: *mut leanh::LeanObject,
    mut v_inst_5893_: *mut leanh::LeanObject,
    mut v_inst_5894_: *mut leanh::LeanObject,
    mut v_inst_5895_: *mut leanh::LeanObject,
    mut v_pre_5896_: *mut leanh::LeanObject,
    mut v_post_5897_: *mut leanh::LeanObject,
    mut v_x_5898_: *mut leanh::LeanObject,
    mut v_x_5899_: *mut leanh::LeanObject,
    mut v___y_5900_: *mut leanh::LeanObject,
    mut v___y_5901_: *mut leanh::LeanObject,
    mut v_binderType_5902_: *mut leanh::LeanObject,
    mut v_body_5903_: *mut leanh::LeanObject,
    mut v_a_5904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_binderInfo_2768__boxed_5905_: u8 = 0;
    let mut v_res_5906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_binderInfo_2768__boxed_5905_ = (leanh::lean_unbox(v_binderInfo_5892_) as u8);
    v_res_5906_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8(
        v_binderName_5890_,
        v_a_5891_,
        v_binderInfo_2768__boxed_5905_,
        v_inst_5893_,
        v_inst_5894_,
        v_inst_5895_,
        v_pre_5896_,
        v_post_5897_,
        v_x_5898_,
        v_x_5899_,
        v___y_5900_,
        v___y_5901_,
        v_binderType_5902_,
        v_body_5903_,
        v_a_5904_,
    );
    leanh::lean_dec_ref(v_body_5903_);
    leanh::lean_dec_ref(v_binderType_5902_);
    leanh::lean_dec(v___y_5900_);
    return v_res_5906_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9(
    mut v_binderName_5907_: *mut leanh::LeanObject,
    mut v_binderInfo_5908_: u8,
    mut v_inst_5909_: *mut leanh::LeanObject,
    mut v_inst_5910_: *mut leanh::LeanObject,
    mut v_inst_5911_: *mut leanh::LeanObject,
    mut v_pre_5912_: *mut leanh::LeanObject,
    mut v_post_5913_: *mut leanh::LeanObject,
    mut v_x_5914_: *mut leanh::LeanObject,
    mut v_x_5915_: *mut leanh::LeanObject,
    mut v___y_5916_: *mut leanh::LeanObject,
    mut v___y_5917_: *mut leanh::LeanObject,
    mut v_binderType_5918_: *mut leanh::LeanObject,
    mut v_body_5919_: *mut leanh::LeanObject,
    mut v_toBind_5920_: *mut leanh::LeanObject,
    mut v_a_5921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5922_ = leanh::lean_box((v_binderInfo_5908_) as usize);
    leanh::lean_inc_ref(v_body_5919_);
    leanh::lean_inc(v___y_5916_);
    leanh::lean_inc(v_x_5915_);
    leanh::lean_inc(v_post_5913_);
    leanh::lean_inc(v_pre_5912_);
    leanh::lean_inc_ref(v_inst_5911_);
    leanh::lean_inc(v_inst_5910_);
    leanh::lean_inc_ref(v_inst_5909_);
    v___f_5923_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8___boxed
            as *mut core::ffi::c_void,
        15,
        14,
    );
    leanh::lean_closure_set(v___f_5923_, 0, v_binderName_5907_);
    leanh::lean_closure_set(v___f_5923_, 1, v_a_5921_);
    leanh::lean_closure_set(v___f_5923_, 2, v___x_5922_);
    leanh::lean_closure_set(v___f_5923_, 3, v_inst_5909_);
    leanh::lean_closure_set(v___f_5923_, 4, v_inst_5910_);
    leanh::lean_closure_set(v___f_5923_, 5, v_inst_5911_);
    leanh::lean_closure_set(v___f_5923_, 6, v_pre_5912_);
    leanh::lean_closure_set(v___f_5923_, 7, v_post_5913_);
    leanh::lean_closure_set(v___f_5923_, 8, v_x_5914_);
    leanh::lean_closure_set(v___f_5923_, 9, v_x_5915_);
    leanh::lean_closure_set(v___f_5923_, 10, v___y_5916_);
    leanh::lean_closure_set(v___f_5923_, 11, v___y_5917_);
    leanh::lean_closure_set(v___f_5923_, 12, v_binderType_5918_);
    leanh::lean_closure_set(v___f_5923_, 13, v_body_5919_);
    v___x_5924_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(
        v_inst_5909_,
        v_inst_5910_,
        v_inst_5911_,
        v_pre_5912_,
        v_post_5913_,
        v_x_5914_,
        v_x_5915_,
        v_body_5919_,
        v___y_5916_,
    );
    v___x_5925_ = leanh::lean_apply_4(
        v_toBind_5920_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5924_,
        v___f_5923_,
    );
    return v___x_5925_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9___boxed(
    mut v_binderName_5926_: *mut leanh::LeanObject,
    mut v_binderInfo_5927_: *mut leanh::LeanObject,
    mut v_inst_5928_: *mut leanh::LeanObject,
    mut v_inst_5929_: *mut leanh::LeanObject,
    mut v_inst_5930_: *mut leanh::LeanObject,
    mut v_pre_5931_: *mut leanh::LeanObject,
    mut v_post_5932_: *mut leanh::LeanObject,
    mut v_x_5933_: *mut leanh::LeanObject,
    mut v_x_5934_: *mut leanh::LeanObject,
    mut v___y_5935_: *mut leanh::LeanObject,
    mut v___y_5936_: *mut leanh::LeanObject,
    mut v_binderType_5937_: *mut leanh::LeanObject,
    mut v_body_5938_: *mut leanh::LeanObject,
    mut v_toBind_5939_: *mut leanh::LeanObject,
    mut v_a_5940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_binderInfo_2629__boxed_5941_: u8 = 0;
    let mut v_res_5942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_binderInfo_2629__boxed_5941_ = (leanh::lean_unbox(v_binderInfo_5927_) as u8);
    v_res_5942_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9(
        v_binderName_5926_,
        v_binderInfo_2629__boxed_5941_,
        v_inst_5928_,
        v_inst_5929_,
        v_inst_5930_,
        v_pre_5931_,
        v_post_5932_,
        v_x_5933_,
        v_x_5934_,
        v___y_5935_,
        v___y_5936_,
        v_binderType_5937_,
        v_body_5938_,
        v_toBind_5939_,
        v_a_5940_,
    );
    leanh::lean_dec(v___y_5935_);
    return v_res_5942_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10(
    mut v_binderName_5943_: *mut leanh::LeanObject,
    mut v_a_5944_: *mut leanh::LeanObject,
    mut v_binderInfo_5945_: u8,
    mut v_inst_5946_: *mut leanh::LeanObject,
    mut v_inst_5947_: *mut leanh::LeanObject,
    mut v_inst_5948_: *mut leanh::LeanObject,
    mut v_pre_5949_: *mut leanh::LeanObject,
    mut v_post_5950_: *mut leanh::LeanObject,
    mut v_x_5951_: *mut leanh::LeanObject,
    mut v_x_5952_: *mut leanh::LeanObject,
    mut v___y_5953_: *mut leanh::LeanObject,
    mut v___y_5954_: *mut leanh::LeanObject,
    mut v_binderType_5955_: *mut leanh::LeanObject,
    mut v_body_5956_: *mut leanh::LeanObject,
    mut v_a_5957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5959_: u8 = 0;
    let mut v___x_5960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: u8 = 0;
    let mut v___x_5963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: usize = 0;
    let mut v___x_5967_: usize = 0;
    let mut v___x_5968_: u8 = 0;
    let mut v___x_5969_: usize = 0;
    let mut v___x_5970_: usize = 0;
    let mut v___x_5971_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5966_ = lean_ptr_addr(v_binderType_5955_);
                v___x_5967_ = lean_ptr_addr(v_a_5944_);
                v___x_5968_ = lean_usize_dec_eq(v___x_5966_, v___x_5967_);
                if v___x_5968_ == 0 {
                    v___y_5959_ = v___x_5968_;
                    state = 1;
                    continue;
                } else {
                    v___x_5969_ = lean_ptr_addr(v_body_5956_);
                    v___x_5970_ = lean_ptr_addr(v_a_5957_);
                    v___x_5971_ = lean_usize_dec_eq(v___x_5969_, v___x_5970_);
                    v___y_5959_ = v___x_5971_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_5959_ == 0 {
                    leanh::lean_dec_ref(v___y_5954_);
                    v___x_5960_ = l_Lean_Expr_lam___override(
                        v_binderName_5943_,
                        v_a_5944_,
                        v_a_5957_,
                        v_binderInfo_5945_,
                    );
                    v___x_5961_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_5946_, v_inst_5947_, v_inst_5948_, v_pre_5949_, v_post_5950_, v_x_5951_, v_x_5952_, v___x_5960_, v___y_5953_);
                    return v___x_5961_;
                } else {
                    v___x_5962_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_5945_, v_binderInfo_5945_);
                    if v___x_5962_ == 0 {
                        leanh::lean_dec_ref(v___y_5954_);
                        v___x_5963_ = l_Lean_Expr_lam___override(
                            v_binderName_5943_,
                            v_a_5944_,
                            v_a_5957_,
                            v_binderInfo_5945_,
                        );
                        v___x_5964_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_5946_, v_inst_5947_, v_inst_5948_, v_pre_5949_, v_post_5950_, v_x_5951_, v_x_5952_, v___x_5963_, v___y_5953_);
                        return v___x_5964_;
                    } else {
                        leanh::lean_dec_ref(v_a_5957_);
                        leanh::lean_dec_ref(v_a_5944_);
                        leanh::lean_dec(v_binderName_5943_);
                        v___x_5965_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_5946_, v_inst_5947_, v_inst_5948_, v_pre_5949_, v_post_5950_, v_x_5951_, v_x_5952_, v___y_5954_, v___y_5953_);
                        return v___x_5965_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10___boxed(
    mut v_binderName_5972_: *mut leanh::LeanObject,
    mut v_a_5973_: *mut leanh::LeanObject,
    mut v_binderInfo_5974_: *mut leanh::LeanObject,
    mut v_inst_5975_: *mut leanh::LeanObject,
    mut v_inst_5976_: *mut leanh::LeanObject,
    mut v_inst_5977_: *mut leanh::LeanObject,
    mut v_pre_5978_: *mut leanh::LeanObject,
    mut v_post_5979_: *mut leanh::LeanObject,
    mut v_x_5980_: *mut leanh::LeanObject,
    mut v_x_5981_: *mut leanh::LeanObject,
    mut v___y_5982_: *mut leanh::LeanObject,
    mut v___y_5983_: *mut leanh::LeanObject,
    mut v_binderType_5984_: *mut leanh::LeanObject,
    mut v_body_5985_: *mut leanh::LeanObject,
    mut v_a_5986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_binderInfo_2743__boxed_5987_: u8 = 0;
    let mut v_res_5988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_binderInfo_2743__boxed_5987_ = (leanh::lean_unbox(v_binderInfo_5974_) as u8);
    v_res_5988_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10(
        v_binderName_5972_,
        v_a_5973_,
        v_binderInfo_2743__boxed_5987_,
        v_inst_5975_,
        v_inst_5976_,
        v_inst_5977_,
        v_pre_5978_,
        v_post_5979_,
        v_x_5980_,
        v_x_5981_,
        v___y_5982_,
        v___y_5983_,
        v_binderType_5984_,
        v_body_5985_,
        v_a_5986_,
    );
    leanh::lean_dec_ref(v_body_5985_);
    leanh::lean_dec_ref(v_binderType_5984_);
    leanh::lean_dec(v___y_5982_);
    return v_res_5988_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11(
    mut v_binderName_5989_: *mut leanh::LeanObject,
    mut v_binderInfo_5990_: u8,
    mut v_inst_5991_: *mut leanh::LeanObject,
    mut v_inst_5992_: *mut leanh::LeanObject,
    mut v_inst_5993_: *mut leanh::LeanObject,
    mut v_pre_5994_: *mut leanh::LeanObject,
    mut v_post_5995_: *mut leanh::LeanObject,
    mut v_x_5996_: *mut leanh::LeanObject,
    mut v_x_5997_: *mut leanh::LeanObject,
    mut v___y_5998_: *mut leanh::LeanObject,
    mut v___y_5999_: *mut leanh::LeanObject,
    mut v_binderType_6000_: *mut leanh::LeanObject,
    mut v_body_6001_: *mut leanh::LeanObject,
    mut v_toBind_6002_: *mut leanh::LeanObject,
    mut v_a_6003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6004_ = leanh::lean_box((v_binderInfo_5990_) as usize);
    leanh::lean_inc_ref(v_body_6001_);
    leanh::lean_inc(v___y_5998_);
    leanh::lean_inc(v_x_5997_);
    leanh::lean_inc(v_post_5995_);
    leanh::lean_inc(v_pre_5994_);
    leanh::lean_inc_ref(v_inst_5993_);
    leanh::lean_inc(v_inst_5992_);
    leanh::lean_inc_ref(v_inst_5991_);
    v___f_6005_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10___boxed
            as *mut core::ffi::c_void,
        15,
        14,
    );
    leanh::lean_closure_set(v___f_6005_, 0, v_binderName_5989_);
    leanh::lean_closure_set(v___f_6005_, 1, v_a_6003_);
    leanh::lean_closure_set(v___f_6005_, 2, v___x_6004_);
    leanh::lean_closure_set(v___f_6005_, 3, v_inst_5991_);
    leanh::lean_closure_set(v___f_6005_, 4, v_inst_5992_);
    leanh::lean_closure_set(v___f_6005_, 5, v_inst_5993_);
    leanh::lean_closure_set(v___f_6005_, 6, v_pre_5994_);
    leanh::lean_closure_set(v___f_6005_, 7, v_post_5995_);
    leanh::lean_closure_set(v___f_6005_, 8, v_x_5996_);
    leanh::lean_closure_set(v___f_6005_, 9, v_x_5997_);
    leanh::lean_closure_set(v___f_6005_, 10, v___y_5998_);
    leanh::lean_closure_set(v___f_6005_, 11, v___y_5999_);
    leanh::lean_closure_set(v___f_6005_, 12, v_binderType_6000_);
    leanh::lean_closure_set(v___f_6005_, 13, v_body_6001_);
    v___x_6006_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(
        v_inst_5991_,
        v_inst_5992_,
        v_inst_5993_,
        v_pre_5994_,
        v_post_5995_,
        v_x_5996_,
        v_x_5997_,
        v_body_6001_,
        v___y_5998_,
    );
    v___x_6007_ = leanh::lean_apply_4(
        v_toBind_6002_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6006_,
        v___f_6005_,
    );
    return v___x_6007_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11___boxed(
    mut v_binderName_6008_: *mut leanh::LeanObject,
    mut v_binderInfo_6009_: *mut leanh::LeanObject,
    mut v_inst_6010_: *mut leanh::LeanObject,
    mut v_inst_6011_: *mut leanh::LeanObject,
    mut v_inst_6012_: *mut leanh::LeanObject,
    mut v_pre_6013_: *mut leanh::LeanObject,
    mut v_post_6014_: *mut leanh::LeanObject,
    mut v_x_6015_: *mut leanh::LeanObject,
    mut v_x_6016_: *mut leanh::LeanObject,
    mut v___y_6017_: *mut leanh::LeanObject,
    mut v___y_6018_: *mut leanh::LeanObject,
    mut v_binderType_6019_: *mut leanh::LeanObject,
    mut v_body_6020_: *mut leanh::LeanObject,
    mut v_toBind_6021_: *mut leanh::LeanObject,
    mut v_a_6022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_binderInfo_2575__boxed_6023_: u8 = 0;
    let mut v_res_6024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_binderInfo_2575__boxed_6023_ = (leanh::lean_unbox(v_binderInfo_6009_) as u8);
    v_res_6024_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11(
        v_binderName_6008_,
        v_binderInfo_2575__boxed_6023_,
        v_inst_6010_,
        v_inst_6011_,
        v_inst_6012_,
        v_pre_6013_,
        v_post_6014_,
        v_x_6015_,
        v_x_6016_,
        v___y_6017_,
        v___y_6018_,
        v_binderType_6019_,
        v_body_6020_,
        v_toBind_6021_,
        v_a_6022_,
    );
    leanh::lean_dec(v___y_6017_);
    return v_res_6024_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12(
    mut v_declName_6025_: *mut leanh::LeanObject,
    mut v_a_6026_: *mut leanh::LeanObject,
    mut v_a_6027_: *mut leanh::LeanObject,
    mut v_nondep_6028_: u8,
    mut v_inst_6029_: *mut leanh::LeanObject,
    mut v_inst_6030_: *mut leanh::LeanObject,
    mut v_inst_6031_: *mut leanh::LeanObject,
    mut v_pre_6032_: *mut leanh::LeanObject,
    mut v_post_6033_: *mut leanh::LeanObject,
    mut v_x_6034_: *mut leanh::LeanObject,
    mut v_x_6035_: *mut leanh::LeanObject,
    mut v___y_6036_: *mut leanh::LeanObject,
    mut v_body_6037_: *mut leanh::LeanObject,
    mut v___y_6038_: *mut leanh::LeanObject,
    mut v_type_6039_: *mut leanh::LeanObject,
    mut v_value_6040_: *mut leanh::LeanObject,
    mut v_a_6041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6043_: u8 = 0;
    let mut v___x_6044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: usize = 0;
    let mut v___x_6047_: usize = 0;
    let mut v___x_6048_: u8 = 0;
    let mut v___x_6049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: usize = 0;
    let mut v___x_6053_: usize = 0;
    let mut v___x_6054_: u8 = 0;
    let mut v___x_6055_: usize = 0;
    let mut v___x_6056_: usize = 0;
    let mut v___x_6057_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6052_ = lean_ptr_addr(v_type_6039_);
                v___x_6053_ = lean_ptr_addr(v_a_6026_);
                v___x_6054_ = lean_usize_dec_eq(v___x_6052_, v___x_6053_);
                if v___x_6054_ == 0 {
                    v___y_6043_ = v___x_6054_;
                    state = 1;
                    continue;
                } else {
                    v___x_6055_ = lean_ptr_addr(v_value_6040_);
                    v___x_6056_ = lean_ptr_addr(v_a_6027_);
                    v___x_6057_ = lean_usize_dec_eq(v___x_6055_, v___x_6056_);
                    v___y_6043_ = v___x_6057_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_6043_ == 0 {
                    leanh::lean_dec_ref(v___y_6038_);
                    v___x_6044_ = l_Lean_Expr_letE___override(
                        v_declName_6025_,
                        v_a_6026_,
                        v_a_6027_,
                        v_a_6041_,
                        v_nondep_6028_,
                    );
                    v___x_6045_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_6029_, v_inst_6030_, v_inst_6031_, v_pre_6032_, v_post_6033_, v_x_6034_, v_x_6035_, v___x_6044_, v___y_6036_);
                    return v___x_6045_;
                } else {
                    v___x_6046_ = lean_ptr_addr(v_body_6037_);
                    v___x_6047_ = lean_ptr_addr(v_a_6041_);
                    v___x_6048_ = lean_usize_dec_eq(v___x_6046_, v___x_6047_);
                    if v___x_6048_ == 0 {
                        leanh::lean_dec_ref(v___y_6038_);
                        v___x_6049_ = l_Lean_Expr_letE___override(
                            v_declName_6025_,
                            v_a_6026_,
                            v_a_6027_,
                            v_a_6041_,
                            v_nondep_6028_,
                        );
                        v___x_6050_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_6029_, v_inst_6030_, v_inst_6031_, v_pre_6032_, v_post_6033_, v_x_6034_, v_x_6035_, v___x_6049_, v___y_6036_);
                        return v___x_6050_;
                    } else {
                        leanh::lean_dec_ref(v_a_6041_);
                        leanh::lean_dec_ref(v_a_6027_);
                        leanh::lean_dec_ref(v_a_6026_);
                        leanh::lean_dec(v_declName_6025_);
                        v___x_6051_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_6029_, v_inst_6030_, v_inst_6031_, v_pre_6032_, v_post_6033_, v_x_6034_, v_x_6035_, v___y_6038_, v___y_6036_);
                        return v___x_6051_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_declName_6058_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_a_6059_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_a_6060_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_nondep_6061_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_inst_6062_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_inst_6063_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_inst_6064_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_pre_6065_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_post_6066_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_x_6067_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_x_6068_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_6069_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_body_6070_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_6071_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_type_6072_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_value_6073_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_a_6074_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_nondep_2793__boxed_6075_: u8 = 0;
    let mut v_res_6076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_2793__boxed_6075_ = (leanh::lean_unbox(v_nondep_6061_) as u8);
    v_res_6076_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12(
        v_declName_6058_,
        v_a_6059_,
        v_a_6060_,
        v_nondep_2793__boxed_6075_,
        v_inst_6062_,
        v_inst_6063_,
        v_inst_6064_,
        v_pre_6065_,
        v_post_6066_,
        v_x_6067_,
        v_x_6068_,
        v___y_6069_,
        v_body_6070_,
        v___y_6071_,
        v_type_6072_,
        v_value_6073_,
        v_a_6074_,
    );
    leanh::lean_dec_ref(v_value_6073_);
    leanh::lean_dec_ref(v_type_6072_);
    leanh::lean_dec_ref(v_body_6070_);
    leanh::lean_dec(v___y_6069_);
    return v_res_6076_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13(
    mut v_declName_6077_: *mut leanh::LeanObject,
    mut v_a_6078_: *mut leanh::LeanObject,
    mut v_nondep_6079_: u8,
    mut v_inst_6080_: *mut leanh::LeanObject,
    mut v_inst_6081_: *mut leanh::LeanObject,
    mut v_inst_6082_: *mut leanh::LeanObject,
    mut v_pre_6083_: *mut leanh::LeanObject,
    mut v_post_6084_: *mut leanh::LeanObject,
    mut v_x_6085_: *mut leanh::LeanObject,
    mut v_x_6086_: *mut leanh::LeanObject,
    mut v___y_6087_: *mut leanh::LeanObject,
    mut v_body_6088_: *mut leanh::LeanObject,
    mut v___y_6089_: *mut leanh::LeanObject,
    mut v_type_6090_: *mut leanh::LeanObject,
    mut v_value_6091_: *mut leanh::LeanObject,
    mut v_toBind_6092_: *mut leanh::LeanObject,
    mut v_a_6093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6094_ = leanh::lean_box((v_nondep_6079_) as usize);
    leanh::lean_inc_ref(v_body_6088_);
    leanh::lean_inc(v___y_6087_);
    leanh::lean_inc(v_x_6086_);
    leanh::lean_inc(v_post_6084_);
    leanh::lean_inc(v_pre_6083_);
    leanh::lean_inc_ref(v_inst_6082_);
    leanh::lean_inc(v_inst_6081_);
    leanh::lean_inc_ref(v_inst_6080_);
    v___f_6095_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12___boxed
            as *mut core::ffi::c_void,
        17,
        16,
    );
    leanh::lean_closure_set(v___f_6095_, 0, v_declName_6077_);
    leanh::lean_closure_set(v___f_6095_, 1, v_a_6078_);
    leanh::lean_closure_set(v___f_6095_, 2, v_a_6093_);
    leanh::lean_closure_set(v___f_6095_, 3, v___x_6094_);
    leanh::lean_closure_set(v___f_6095_, 4, v_inst_6080_);
    leanh::lean_closure_set(v___f_6095_, 5, v_inst_6081_);
    leanh::lean_closure_set(v___f_6095_, 6, v_inst_6082_);
    leanh::lean_closure_set(v___f_6095_, 7, v_pre_6083_);
    leanh::lean_closure_set(v___f_6095_, 8, v_post_6084_);
    leanh::lean_closure_set(v___f_6095_, 9, v_x_6085_);
    leanh::lean_closure_set(v___f_6095_, 10, v_x_6086_);
    leanh::lean_closure_set(v___f_6095_, 11, v___y_6087_);
    leanh::lean_closure_set(v___f_6095_, 12, v_body_6088_);
    leanh::lean_closure_set(v___f_6095_, 13, v___y_6089_);
    leanh::lean_closure_set(v___f_6095_, 14, v_type_6090_);
    leanh::lean_closure_set(v___f_6095_, 15, v_value_6091_);
    v___x_6096_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(
        v_inst_6080_,
        v_inst_6081_,
        v_inst_6082_,
        v_pre_6083_,
        v_post_6084_,
        v_x_6085_,
        v_x_6086_,
        v_body_6088_,
        v___y_6087_,
    );
    v___x_6097_ = leanh::lean_apply_4(
        v_toBind_6092_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6096_,
        v___f_6095_,
    );
    return v___x_6097_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_declName_6098_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_a_6099_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_nondep_6100_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_inst_6101_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_inst_6102_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_inst_6103_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_pre_6104_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_post_6105_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_x_6106_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_x_6107_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_6108_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_body_6109_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_6110_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_type_6111_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_value_6112_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_toBind_6113_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_a_6114_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_nondep_2589__boxed_6115_: u8 = 0;
    let mut v_res_6116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_2589__boxed_6115_ = (leanh::lean_unbox(v_nondep_6100_) as u8);
    v_res_6116_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13(
        v_declName_6098_,
        v_a_6099_,
        v_nondep_2589__boxed_6115_,
        v_inst_6101_,
        v_inst_6102_,
        v_inst_6103_,
        v_pre_6104_,
        v_post_6105_,
        v_x_6106_,
        v_x_6107_,
        v___y_6108_,
        v_body_6109_,
        v___y_6110_,
        v_type_6111_,
        v_value_6112_,
        v_toBind_6113_,
        v_a_6114_,
    );
    leanh::lean_dec(v___y_6108_);
    return v_res_6116_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14(
    mut v_declName_6117_: *mut leanh::LeanObject,
    mut v_nondep_6118_: u8,
    mut v_inst_6119_: *mut leanh::LeanObject,
    mut v_inst_6120_: *mut leanh::LeanObject,
    mut v_inst_6121_: *mut leanh::LeanObject,
    mut v_pre_6122_: *mut leanh::LeanObject,
    mut v_post_6123_: *mut leanh::LeanObject,
    mut v_x_6124_: *mut leanh::LeanObject,
    mut v_x_6125_: *mut leanh::LeanObject,
    mut v___y_6126_: *mut leanh::LeanObject,
    mut v_body_6127_: *mut leanh::LeanObject,
    mut v___y_6128_: *mut leanh::LeanObject,
    mut v_type_6129_: *mut leanh::LeanObject,
    mut v_value_6130_: *mut leanh::LeanObject,
    mut v_toBind_6131_: *mut leanh::LeanObject,
    mut v_a_6132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6133_ = leanh::lean_box((v_nondep_6118_) as usize);
    leanh::lean_inc(v_toBind_6131_);
    leanh::lean_inc_ref(v_value_6130_);
    leanh::lean_inc(v___y_6126_);
    leanh::lean_inc(v_x_6125_);
    leanh::lean_inc(v_post_6123_);
    leanh::lean_inc(v_pre_6122_);
    leanh::lean_inc_ref(v_inst_6121_);
    leanh::lean_inc(v_inst_6120_);
    leanh::lean_inc_ref(v_inst_6119_);
    v___f_6134_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13___boxed
            as *mut core::ffi::c_void,
        17,
        16,
    );
    leanh::lean_closure_set(v___f_6134_, 0, v_declName_6117_);
    leanh::lean_closure_set(v___f_6134_, 1, v_a_6132_);
    leanh::lean_closure_set(v___f_6134_, 2, v___x_6133_);
    leanh::lean_closure_set(v___f_6134_, 3, v_inst_6119_);
    leanh::lean_closure_set(v___f_6134_, 4, v_inst_6120_);
    leanh::lean_closure_set(v___f_6134_, 5, v_inst_6121_);
    leanh::lean_closure_set(v___f_6134_, 6, v_pre_6122_);
    leanh::lean_closure_set(v___f_6134_, 7, v_post_6123_);
    leanh::lean_closure_set(v___f_6134_, 8, v_x_6124_);
    leanh::lean_closure_set(v___f_6134_, 9, v_x_6125_);
    leanh::lean_closure_set(v___f_6134_, 10, v___y_6126_);
    leanh::lean_closure_set(v___f_6134_, 11, v_body_6127_);
    leanh::lean_closure_set(v___f_6134_, 12, v___y_6128_);
    leanh::lean_closure_set(v___f_6134_, 13, v_type_6129_);
    leanh::lean_closure_set(v___f_6134_, 14, v_value_6130_);
    leanh::lean_closure_set(v___f_6134_, 15, v_toBind_6131_);
    v___x_6135_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(
        v_inst_6119_,
        v_inst_6120_,
        v_inst_6121_,
        v_pre_6122_,
        v_post_6123_,
        v_x_6124_,
        v_x_6125_,
        v_value_6130_,
        v___y_6126_,
    );
    v___x_6136_ = leanh::lean_apply_4(
        v_toBind_6131_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6135_,
        v___f_6134_,
    );
    return v___x_6136_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14___boxed(
    mut v_declName_6137_: *mut leanh::LeanObject,
    mut v_nondep_6138_: *mut leanh::LeanObject,
    mut v_inst_6139_: *mut leanh::LeanObject,
    mut v_inst_6140_: *mut leanh::LeanObject,
    mut v_inst_6141_: *mut leanh::LeanObject,
    mut v_pre_6142_: *mut leanh::LeanObject,
    mut v_post_6143_: *mut leanh::LeanObject,
    mut v_x_6144_: *mut leanh::LeanObject,
    mut v_x_6145_: *mut leanh::LeanObject,
    mut v___y_6146_: *mut leanh::LeanObject,
    mut v_body_6147_: *mut leanh::LeanObject,
    mut v___y_6148_: *mut leanh::LeanObject,
    mut v_type_6149_: *mut leanh::LeanObject,
    mut v_value_6150_: *mut leanh::LeanObject,
    mut v_toBind_6151_: *mut leanh::LeanObject,
    mut v_a_6152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_nondep_2604__boxed_6153_: u8 = 0;
    let mut v_res_6154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_2604__boxed_6153_ = (leanh::lean_unbox(v_nondep_6138_) as u8);
    v_res_6154_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14(
        v_declName_6137_,
        v_nondep_2604__boxed_6153_,
        v_inst_6139_,
        v_inst_6140_,
        v_inst_6141_,
        v_pre_6142_,
        v_post_6143_,
        v_x_6144_,
        v_x_6145_,
        v___y_6146_,
        v_body_6147_,
        v___y_6148_,
        v_type_6149_,
        v_value_6150_,
        v_toBind_6151_,
        v_a_6152_,
    );
    leanh::lean_dec(v___y_6146_);
    return v_res_6154_;
}
pub unsafe fn _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_6155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_6156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6155_ = leanh::lean_box(0);
    v_dummy_6156_ = l_Lean_Expr_sort___override(v___x_6155_);
    return v_dummy_6156_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15(
    mut v_expr_6157_: *mut leanh::LeanObject,
    mut v_data_6158_: *mut leanh::LeanObject,
    mut v_inst_6159_: *mut leanh::LeanObject,
    mut v_inst_6160_: *mut leanh::LeanObject,
    mut v_inst_6161_: *mut leanh::LeanObject,
    mut v_pre_6162_: *mut leanh::LeanObject,
    mut v_post_6163_: *mut leanh::LeanObject,
    mut v_x_6164_: *mut leanh::LeanObject,
    mut v_x_6165_: *mut leanh::LeanObject,
    mut v___y_6166_: *mut leanh::LeanObject,
    mut v___y_6167_: *mut leanh::LeanObject,
    mut v_a_6168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6169_: usize = 0;
    let mut v___x_6170_: usize = 0;
    let mut v___x_6171_: u8 = 0;
    v___x_6169_ = lean_ptr_addr(v_expr_6157_);
    v___x_6170_ = lean_ptr_addr(v_a_6168_);
    v___x_6171_ = lean_usize_dec_eq(v___x_6169_, v___x_6170_);
    if v___x_6171_ == 0 {
        let mut v___x_6172_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6173_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___y_6167_);
        v___x_6172_ = l_Lean_Expr_mdata___override(v_data_6158_, v_a_6168_);
        v___x_6173_ =
            l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(
                v_inst_6159_,
                v_inst_6160_,
                v_inst_6161_,
                v_pre_6162_,
                v_post_6163_,
                v_x_6164_,
                v_x_6165_,
                v___x_6172_,
                v___y_6166_,
            );
        return v___x_6173_;
    } else {
        let mut v___x_6174_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_a_6168_);
        leanh::lean_dec(v_data_6158_);
        v___x_6174_ =
            l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(
                v_inst_6159_,
                v_inst_6160_,
                v_inst_6161_,
                v_pre_6162_,
                v_post_6163_,
                v_x_6164_,
                v_x_6165_,
                v___y_6167_,
                v___y_6166_,
            );
        return v___x_6174_;
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15___boxed(
    mut v_expr_6175_: *mut leanh::LeanObject,
    mut v_data_6176_: *mut leanh::LeanObject,
    mut v_inst_6177_: *mut leanh::LeanObject,
    mut v_inst_6178_: *mut leanh::LeanObject,
    mut v_inst_6179_: *mut leanh::LeanObject,
    mut v_pre_6180_: *mut leanh::LeanObject,
    mut v_post_6181_: *mut leanh::LeanObject,
    mut v_x_6182_: *mut leanh::LeanObject,
    mut v_x_6183_: *mut leanh::LeanObject,
    mut v___y_6184_: *mut leanh::LeanObject,
    mut v___y_6185_: *mut leanh::LeanObject,
    mut v_a_6186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6187_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15(
        v_expr_6175_,
        v_data_6176_,
        v_inst_6177_,
        v_inst_6178_,
        v_inst_6179_,
        v_pre_6180_,
        v_post_6181_,
        v_x_6182_,
        v_x_6183_,
        v___y_6184_,
        v___y_6185_,
        v_a_6186_,
    );
    leanh::lean_dec(v___y_6184_);
    leanh::lean_dec_ref(v_expr_6175_);
    return v_res_6187_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16(
    mut v_struct_6188_: *mut leanh::LeanObject,
    mut v_typeName_6189_: *mut leanh::LeanObject,
    mut v_idx_6190_: *mut leanh::LeanObject,
    mut v_inst_6191_: *mut leanh::LeanObject,
    mut v_inst_6192_: *mut leanh::LeanObject,
    mut v_inst_6193_: *mut leanh::LeanObject,
    mut v_pre_6194_: *mut leanh::LeanObject,
    mut v_post_6195_: *mut leanh::LeanObject,
    mut v_x_6196_: *mut leanh::LeanObject,
    mut v_x_6197_: *mut leanh::LeanObject,
    mut v___y_6198_: *mut leanh::LeanObject,
    mut v___y_6199_: *mut leanh::LeanObject,
    mut v_a_6200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6201_: usize = 0;
    let mut v___x_6202_: usize = 0;
    let mut v___x_6203_: u8 = 0;
    v___x_6201_ = lean_ptr_addr(v_struct_6188_);
    v___x_6202_ = lean_ptr_addr(v_a_6200_);
    v___x_6203_ = lean_usize_dec_eq(v___x_6201_, v___x_6202_);
    if v___x_6203_ == 0 {
        let mut v___x_6204_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6205_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___y_6199_);
        v___x_6204_ = l_Lean_Expr_proj___override(v_typeName_6189_, v_idx_6190_, v_a_6200_);
        v___x_6205_ =
            l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(
                v_inst_6191_,
                v_inst_6192_,
                v_inst_6193_,
                v_pre_6194_,
                v_post_6195_,
                v_x_6196_,
                v_x_6197_,
                v___x_6204_,
                v___y_6198_,
            );
        return v___x_6205_;
    } else {
        let mut v___x_6206_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_a_6200_);
        leanh::lean_dec(v_idx_6190_);
        leanh::lean_dec(v_typeName_6189_);
        v___x_6206_ =
            l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(
                v_inst_6191_,
                v_inst_6192_,
                v_inst_6193_,
                v_pre_6194_,
                v_post_6195_,
                v_x_6196_,
                v_x_6197_,
                v___y_6199_,
                v___y_6198_,
            );
        return v___x_6206_;
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16___boxed(
    mut v_struct_6207_: *mut leanh::LeanObject,
    mut v_typeName_6208_: *mut leanh::LeanObject,
    mut v_idx_6209_: *mut leanh::LeanObject,
    mut v_inst_6210_: *mut leanh::LeanObject,
    mut v_inst_6211_: *mut leanh::LeanObject,
    mut v_inst_6212_: *mut leanh::LeanObject,
    mut v_pre_6213_: *mut leanh::LeanObject,
    mut v_post_6214_: *mut leanh::LeanObject,
    mut v_x_6215_: *mut leanh::LeanObject,
    mut v_x_6216_: *mut leanh::LeanObject,
    mut v___y_6217_: *mut leanh::LeanObject,
    mut v___y_6218_: *mut leanh::LeanObject,
    mut v_a_6219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6220_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16(
        v_struct_6207_,
        v_typeName_6208_,
        v_idx_6209_,
        v_inst_6210_,
        v_inst_6211_,
        v_inst_6212_,
        v_pre_6213_,
        v_post_6214_,
        v_x_6215_,
        v_x_6216_,
        v___y_6217_,
        v___y_6218_,
        v_a_6219_,
    );
    leanh::lean_dec(v___y_6217_);
    leanh::lean_dec_ref(v_struct_6207_);
    return v_res_6220_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17(
    mut v_toApplicative_6221_: *mut leanh::LeanObject,
    mut v_inst_6222_: *mut leanh::LeanObject,
    mut v_inst_6223_: *mut leanh::LeanObject,
    mut v_inst_6224_: *mut leanh::LeanObject,
    mut v_pre_6225_: *mut leanh::LeanObject,
    mut v_post_6226_: *mut leanh::LeanObject,
    mut v_x_6227_: *mut leanh::LeanObject,
    mut v_x_6228_: *mut leanh::LeanObject,
    mut v___y_6229_: *mut leanh::LeanObject,
    mut v_toBind_6230_: *mut leanh::LeanObject,
    mut v___f_6231_: *mut leanh::LeanObject,
    mut v___f_6232_: *mut leanh::LeanObject,
    mut v_e_6233_: *mut leanh::LeanObject,
    mut v_a_6234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_6237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_6238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_6240_: u8 = 0;
    let mut v___x_6241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_6245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_6246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_6248_: u8 = 0;
    let mut v___x_6249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_6253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_6257_: u8 = 0;
    let mut v___x_6258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_6262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_6263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405__overap_6267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_6269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_6270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_6274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_6276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_6281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_6284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_6287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_a_6234_) {
                0 => {
                    leanh::lean_dec_ref(v_e_6233_);
                    leanh::lean_dec(v___f_6232_);
                    leanh::lean_dec(v___f_6231_);
                    leanh::lean_dec(v_toBind_6230_);
                    leanh::lean_dec(v_x_6228_);
                    leanh::lean_dec(v_post_6226_);
                    leanh::lean_dec(v_pre_6225_);
                    leanh::lean_dec_ref(v_inst_6224_);
                    leanh::lean_dec(v_inst_6223_);
                    leanh::lean_dec_ref(v_inst_6222_);
                    v_e_6281_ = leanh::lean_ctor_get(v_a_6234_, 0);
                    leanh::lean_inc_ref(v_e_6281_);
                    leanh::lean_dec_ref_known(v_a_6234_, 1);
                    v_toPure_6282_ = leanh::lean_ctor_get(v_toApplicative_6221_, 1);
                    leanh::lean_inc(v_toPure_6282_);
                    leanh::lean_dec_ref(v_toApplicative_6221_);
                    v___x_6283_ = leanh::lean_apply_2(
                        v_toPure_6282_,
                        leanh::lean_box(0),
                        v_e_6281_,
                    );
                    return v___x_6283_;
                }
                1 => {
                    leanh::lean_dec_ref(v_e_6233_);
                    leanh::lean_dec(v___f_6232_);
                    leanh::lean_dec_ref(v_toApplicative_6221_);
                    v_e_6284_ = leanh::lean_ctor_get(v_a_6234_, 0);
                    leanh::lean_inc_ref(v_e_6284_);
                    leanh::lean_dec_ref_known(v_a_6234_, 1);
                    v___x_6285_ =
                        l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(
                            v_inst_6222_,
                            v_inst_6223_,
                            v_inst_6224_,
                            v_pre_6225_,
                            v_post_6226_,
                            v_x_6227_,
                            v_x_6228_,
                            v_e_6284_,
                            v___y_6229_,
                        );
                    v___x_6286_ = leanh::lean_apply_4(
                        v_toBind_6230_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_6285_,
                        v___f_6231_,
                    );
                    return v___x_6286_;
                }
                _ => {
                    leanh::lean_dec(v___f_6231_);
                    leanh::lean_dec_ref(v_toApplicative_6221_);
                    v_e_x3f_6287_ = leanh::lean_ctor_get(v_a_6234_, 0);
                    leanh::lean_inc(v_e_x3f_6287_);
                    leanh::lean_dec_ref_known(v_a_6234_, 1);
                    if leanh::lean_obj_tag(v_e_x3f_6287_) == 0 {
                        v___y_6236_ = v_e_6233_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_e_6233_);
                        v_val_6288_ = leanh::lean_ctor_get(v_e_x3f_6287_, 0);
                        leanh::lean_inc(v_val_6288_);
                        leanh::lean_dec_ref_known(v_e_x3f_6287_, 1);
                        v___y_6236_ = v_val_6288_;
                        state = 1;
                        continue;
                    }
                }
            },
            1 => match leanh::lean_obj_tag(v___y_6236_) {
                7 => {
                    leanh::lean_dec(v___f_6232_);
                    v_binderName_6237_ = leanh::lean_ctor_get(v___y_6236_, 0);
                    leanh::lean_inc(v_binderName_6237_);
                    v_binderType_6238_ = leanh::lean_ctor_get(v___y_6236_, 1);
                    leanh::lean_inc_ref_n(v_binderType_6238_, 2);
                    v_body_6239_ = leanh::lean_ctor_get(v___y_6236_, 2);
                    leanh::lean_inc_ref(v_body_6239_);
                    v_binderInfo_6240_ = leanh::lean_ctor_get_uint8(
                        v___y_6236_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    v___x_6241_ = leanh::lean_box((v_binderInfo_6240_) as usize);
                    leanh::lean_inc(v_toBind_6230_);
                    leanh::lean_inc(v___y_6229_);
                    leanh::lean_inc(v_x_6228_);
                    leanh::lean_inc(v_post_6226_);
                    leanh::lean_inc(v_pre_6225_);
                    leanh::lean_inc_ref(v_inst_6224_);
                    leanh::lean_inc(v_inst_6223_);
                    leanh::lean_inc_ref(v_inst_6222_);
                    v___f_6242_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9___boxed as *mut core::ffi::c_void, 15, 14);
                    leanh::lean_closure_set(v___f_6242_, 0, v_binderName_6237_);
                    leanh::lean_closure_set(v___f_6242_, 1, v___x_6241_);
                    leanh::lean_closure_set(v___f_6242_, 2, v_inst_6222_);
                    leanh::lean_closure_set(v___f_6242_, 3, v_inst_6223_);
                    leanh::lean_closure_set(v___f_6242_, 4, v_inst_6224_);
                    leanh::lean_closure_set(v___f_6242_, 5, v_pre_6225_);
                    leanh::lean_closure_set(v___f_6242_, 6, v_post_6226_);
                    leanh::lean_closure_set(v___f_6242_, 7, v_x_6227_);
                    leanh::lean_closure_set(v___f_6242_, 8, v_x_6228_);
                    leanh::lean_closure_set(v___f_6242_, 9, v___y_6229_);
                    leanh::lean_closure_set(v___f_6242_, 10, v___y_6236_);
                    leanh::lean_closure_set(v___f_6242_, 11, v_binderType_6238_);
                    leanh::lean_closure_set(v___f_6242_, 12, v_body_6239_);
                    leanh::lean_closure_set(v___f_6242_, 13, v_toBind_6230_);
                    v___x_6243_ =
                        l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(
                            v_inst_6222_,
                            v_inst_6223_,
                            v_inst_6224_,
                            v_pre_6225_,
                            v_post_6226_,
                            v_x_6227_,
                            v_x_6228_,
                            v_binderType_6238_,
                            v___y_6229_,
                        );
                    v___x_6244_ = leanh::lean_apply_4(
                        v_toBind_6230_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_6243_,
                        v___f_6242_,
                    );
                    return v___x_6244_;
                }
                6 => {
                    leanh::lean_dec(v___f_6232_);
                    v_binderName_6245_ = leanh::lean_ctor_get(v___y_6236_, 0);
                    leanh::lean_inc(v_binderName_6245_);
                    v_binderType_6246_ = leanh::lean_ctor_get(v___y_6236_, 1);
                    leanh::lean_inc_ref_n(v_binderType_6246_, 2);
                    v_body_6247_ = leanh::lean_ctor_get(v___y_6236_, 2);
                    leanh::lean_inc_ref(v_body_6247_);
                    v_binderInfo_6248_ = leanh::lean_ctor_get_uint8(
                        v___y_6236_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    v___x_6249_ = leanh::lean_box((v_binderInfo_6248_) as usize);
                    leanh::lean_inc(v_toBind_6230_);
                    leanh::lean_inc(v___y_6229_);
                    leanh::lean_inc(v_x_6228_);
                    leanh::lean_inc(v_post_6226_);
                    leanh::lean_inc(v_pre_6225_);
                    leanh::lean_inc_ref(v_inst_6224_);
                    leanh::lean_inc(v_inst_6223_);
                    leanh::lean_inc_ref(v_inst_6222_);
                    v___f_6250_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11___boxed as *mut core::ffi::c_void, 15, 14);
                    leanh::lean_closure_set(v___f_6250_, 0, v_binderName_6245_);
                    leanh::lean_closure_set(v___f_6250_, 1, v___x_6249_);
                    leanh::lean_closure_set(v___f_6250_, 2, v_inst_6222_);
                    leanh::lean_closure_set(v___f_6250_, 3, v_inst_6223_);
                    leanh::lean_closure_set(v___f_6250_, 4, v_inst_6224_);
                    leanh::lean_closure_set(v___f_6250_, 5, v_pre_6225_);
                    leanh::lean_closure_set(v___f_6250_, 6, v_post_6226_);
                    leanh::lean_closure_set(v___f_6250_, 7, v_x_6227_);
                    leanh::lean_closure_set(v___f_6250_, 8, v_x_6228_);
                    leanh::lean_closure_set(v___f_6250_, 9, v___y_6229_);
                    leanh::lean_closure_set(v___f_6250_, 10, v___y_6236_);
                    leanh::lean_closure_set(v___f_6250_, 11, v_binderType_6246_);
                    leanh::lean_closure_set(v___f_6250_, 12, v_body_6247_);
                    leanh::lean_closure_set(v___f_6250_, 13, v_toBind_6230_);
                    v___x_6251_ =
                        l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(
                            v_inst_6222_,
                            v_inst_6223_,
                            v_inst_6224_,
                            v_pre_6225_,
                            v_post_6226_,
                            v_x_6227_,
                            v_x_6228_,
                            v_binderType_6246_,
                            v___y_6229_,
                        );
                    v___x_6252_ = leanh::lean_apply_4(
                        v_toBind_6230_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_6251_,
                        v___f_6250_,
                    );
                    return v___x_6252_;
                }
                8 => {
                    leanh::lean_dec(v___f_6232_);
                    v_declName_6253_ = leanh::lean_ctor_get(v___y_6236_, 0);
                    leanh::lean_inc(v_declName_6253_);
                    v_type_6254_ = leanh::lean_ctor_get(v___y_6236_, 1);
                    leanh::lean_inc_ref_n(v_type_6254_, 2);
                    v_value_6255_ = leanh::lean_ctor_get(v___y_6236_, 2);
                    leanh::lean_inc_ref(v_value_6255_);
                    v_body_6256_ = leanh::lean_ctor_get(v___y_6236_, 3);
                    leanh::lean_inc_ref(v_body_6256_);
                    v_nondep_6257_ = leanh::lean_ctor_get_uint8(
                        v___y_6236_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    v___x_6258_ = leanh::lean_box((v_nondep_6257_) as usize);
                    leanh::lean_inc(v_toBind_6230_);
                    leanh::lean_inc(v___y_6229_);
                    leanh::lean_inc(v_x_6228_);
                    leanh::lean_inc(v_post_6226_);
                    leanh::lean_inc(v_pre_6225_);
                    leanh::lean_inc_ref(v_inst_6224_);
                    leanh::lean_inc(v_inst_6223_);
                    leanh::lean_inc_ref(v_inst_6222_);
                    v___f_6259_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14___boxed as *mut core::ffi::c_void, 16, 15);
                    leanh::lean_closure_set(v___f_6259_, 0, v_declName_6253_);
                    leanh::lean_closure_set(v___f_6259_, 1, v___x_6258_);
                    leanh::lean_closure_set(v___f_6259_, 2, v_inst_6222_);
                    leanh::lean_closure_set(v___f_6259_, 3, v_inst_6223_);
                    leanh::lean_closure_set(v___f_6259_, 4, v_inst_6224_);
                    leanh::lean_closure_set(v___f_6259_, 5, v_pre_6225_);
                    leanh::lean_closure_set(v___f_6259_, 6, v_post_6226_);
                    leanh::lean_closure_set(v___f_6259_, 7, v_x_6227_);
                    leanh::lean_closure_set(v___f_6259_, 8, v_x_6228_);
                    leanh::lean_closure_set(v___f_6259_, 9, v___y_6229_);
                    leanh::lean_closure_set(v___f_6259_, 10, v_body_6256_);
                    leanh::lean_closure_set(v___f_6259_, 11, v___y_6236_);
                    leanh::lean_closure_set(v___f_6259_, 12, v_type_6254_);
                    leanh::lean_closure_set(v___f_6259_, 13, v_value_6255_);
                    leanh::lean_closure_set(v___f_6259_, 14, v_toBind_6230_);
                    v___x_6260_ =
                        l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(
                            v_inst_6222_,
                            v_inst_6223_,
                            v_inst_6224_,
                            v_pre_6225_,
                            v_post_6226_,
                            v_x_6227_,
                            v_x_6228_,
                            v_type_6254_,
                            v___y_6229_,
                        );
                    v___x_6261_ = leanh::lean_apply_4(
                        v_toBind_6230_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_6260_,
                        v___f_6259_,
                    );
                    return v___x_6261_;
                }
                5 => {
                    leanh::lean_dec(v_toBind_6230_);
                    leanh::lean_dec(v_x_6228_);
                    leanh::lean_dec(v_post_6226_);
                    leanh::lean_dec(v_pre_6225_);
                    leanh::lean_dec_ref(v_inst_6224_);
                    leanh::lean_dec(v_inst_6223_);
                    leanh::lean_dec_ref(v_inst_6222_);
                    v_dummy_6262_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once), _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
                    v_nargs_6263_ = l_Lean_Expr_getAppNumArgs(v___y_6236_);
                    leanh::lean_inc(v_nargs_6263_);
                    v___x_6264_ = lean_mk_array(v_nargs_6263_, v_dummy_6262_);
                    v___x_6265_ = leanh::lean_unsigned_to_nat(1);
                    v___x_6266_ = lean_nat_sub(v_nargs_6263_, v___x_6265_);
                    leanh::lean_dec(v_nargs_6263_);
                    v___x_2405__overap_6267_ = l_Lean_Expr_withAppAux___redArg(
                        v___f_6232_,
                        v___y_6236_,
                        v___x_6264_,
                        v___x_6266_,
                    );
                    leanh::lean_inc(v___y_6229_);
                    v___x_6268_ = leanh::lean_apply_1(v___x_2405__overap_6267_, v___y_6229_);
                    return v___x_6268_;
                }
                10 => {
                    leanh::lean_dec(v___f_6232_);
                    v_data_6269_ = leanh::lean_ctor_get(v___y_6236_, 0);
                    leanh::lean_inc(v_data_6269_);
                    v_expr_6270_ = leanh::lean_ctor_get(v___y_6236_, 1);
                    leanh::lean_inc_ref_n(v_expr_6270_, 2);
                    leanh::lean_inc(v___y_6229_);
                    leanh::lean_inc(v_x_6228_);
                    leanh::lean_inc(v_post_6226_);
                    leanh::lean_inc(v_pre_6225_);
                    leanh::lean_inc_ref(v_inst_6224_);
                    leanh::lean_inc(v_inst_6223_);
                    leanh::lean_inc_ref(v_inst_6222_);
                    v___f_6271_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15___boxed as *mut core::ffi::c_void, 12, 11);
                    leanh::lean_closure_set(v___f_6271_, 0, v_expr_6270_);
                    leanh::lean_closure_set(v___f_6271_, 1, v_data_6269_);
                    leanh::lean_closure_set(v___f_6271_, 2, v_inst_6222_);
                    leanh::lean_closure_set(v___f_6271_, 3, v_inst_6223_);
                    leanh::lean_closure_set(v___f_6271_, 4, v_inst_6224_);
                    leanh::lean_closure_set(v___f_6271_, 5, v_pre_6225_);
                    leanh::lean_closure_set(v___f_6271_, 6, v_post_6226_);
                    leanh::lean_closure_set(v___f_6271_, 7, v_x_6227_);
                    leanh::lean_closure_set(v___f_6271_, 8, v_x_6228_);
                    leanh::lean_closure_set(v___f_6271_, 9, v___y_6229_);
                    leanh::lean_closure_set(v___f_6271_, 10, v___y_6236_);
                    v___x_6272_ =
                        l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(
                            v_inst_6222_,
                            v_inst_6223_,
                            v_inst_6224_,
                            v_pre_6225_,
                            v_post_6226_,
                            v_x_6227_,
                            v_x_6228_,
                            v_expr_6270_,
                            v___y_6229_,
                        );
                    v___x_6273_ = leanh::lean_apply_4(
                        v_toBind_6230_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_6272_,
                        v___f_6271_,
                    );
                    return v___x_6273_;
                }
                11 => {
                    leanh::lean_dec(v___f_6232_);
                    v_typeName_6274_ = leanh::lean_ctor_get(v___y_6236_, 0);
                    leanh::lean_inc(v_typeName_6274_);
                    v_idx_6275_ = leanh::lean_ctor_get(v___y_6236_, 1);
                    leanh::lean_inc(v_idx_6275_);
                    v_struct_6276_ = leanh::lean_ctor_get(v___y_6236_, 2);
                    leanh::lean_inc_ref_n(v_struct_6276_, 2);
                    leanh::lean_inc(v___y_6229_);
                    leanh::lean_inc(v_x_6228_);
                    leanh::lean_inc(v_post_6226_);
                    leanh::lean_inc(v_pre_6225_);
                    leanh::lean_inc_ref(v_inst_6224_);
                    leanh::lean_inc(v_inst_6223_);
                    leanh::lean_inc_ref(v_inst_6222_);
                    v___f_6277_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16___boxed as *mut core::ffi::c_void, 13, 12);
                    leanh::lean_closure_set(v___f_6277_, 0, v_struct_6276_);
                    leanh::lean_closure_set(v___f_6277_, 1, v_typeName_6274_);
                    leanh::lean_closure_set(v___f_6277_, 2, v_idx_6275_);
                    leanh::lean_closure_set(v___f_6277_, 3, v_inst_6222_);
                    leanh::lean_closure_set(v___f_6277_, 4, v_inst_6223_);
                    leanh::lean_closure_set(v___f_6277_, 5, v_inst_6224_);
                    leanh::lean_closure_set(v___f_6277_, 6, v_pre_6225_);
                    leanh::lean_closure_set(v___f_6277_, 7, v_post_6226_);
                    leanh::lean_closure_set(v___f_6277_, 8, v_x_6227_);
                    leanh::lean_closure_set(v___f_6277_, 9, v_x_6228_);
                    leanh::lean_closure_set(v___f_6277_, 10, v___y_6229_);
                    leanh::lean_closure_set(v___f_6277_, 11, v___y_6236_);
                    v___x_6278_ =
                        l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(
                            v_inst_6222_,
                            v_inst_6223_,
                            v_inst_6224_,
                            v_pre_6225_,
                            v_post_6226_,
                            v_x_6227_,
                            v_x_6228_,
                            v_struct_6276_,
                            v___y_6229_,
                        );
                    v___x_6279_ = leanh::lean_apply_4(
                        v_toBind_6230_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_6278_,
                        v___f_6277_,
                    );
                    return v___x_6279_;
                }
                _ => {
                    leanh::lean_dec(v___f_6232_);
                    leanh::lean_dec(v_toBind_6230_);
                    v___x_6280_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_6222_, v_inst_6223_, v_inst_6224_, v_pre_6225_, v_post_6226_, v_x_6227_, v_x_6228_, v___y_6236_, v___y_6229_);
                    return v___x_6280_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___boxed(
    mut v_toApplicative_6289_: *mut leanh::LeanObject,
    mut v_inst_6290_: *mut leanh::LeanObject,
    mut v_inst_6291_: *mut leanh::LeanObject,
    mut v_inst_6292_: *mut leanh::LeanObject,
    mut v_pre_6293_: *mut leanh::LeanObject,
    mut v_post_6294_: *mut leanh::LeanObject,
    mut v_x_6295_: *mut leanh::LeanObject,
    mut v_x_6296_: *mut leanh::LeanObject,
    mut v___y_6297_: *mut leanh::LeanObject,
    mut v_toBind_6298_: *mut leanh::LeanObject,
    mut v___f_6299_: *mut leanh::LeanObject,
    mut v___f_6300_: *mut leanh::LeanObject,
    mut v_e_6301_: *mut leanh::LeanObject,
    mut v_a_6302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6303_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17(
        v_toApplicative_6289_,
        v_inst_6290_,
        v_inst_6291_,
        v_inst_6292_,
        v_pre_6293_,
        v_post_6294_,
        v_x_6295_,
        v_x_6296_,
        v___y_6297_,
        v_toBind_6298_,
        v___f_6299_,
        v___f_6300_,
        v_e_6301_,
        v_a_6302_,
    );
    leanh::lean_dec(v___y_6297_);
    return v_res_6303_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18(
    mut v_inst_6304_: *mut leanh::LeanObject,
    mut v_inst_6305_: *mut leanh::LeanObject,
    mut v_inst_6306_: *mut leanh::LeanObject,
    mut v_pre_6307_: *mut leanh::LeanObject,
    mut v_post_6308_: *mut leanh::LeanObject,
    mut v_x_6309_: *mut leanh::LeanObject,
    mut v_x_6310_: *mut leanh::LeanObject,
    mut v_toApplicative_6311_: *mut leanh::LeanObject,
    mut v_toBind_6312_: *mut leanh::LeanObject,
    mut v___f_6313_: *mut leanh::LeanObject,
    mut v_e_6314_: *mut leanh::LeanObject,
    mut v_____r_6315_: *mut leanh::LeanObject,
    mut v___y_6316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6320_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_n(v___y_6316_, 2);
    leanh::lean_inc(v_x_6310_);
    leanh::lean_inc(v_post_6308_);
    leanh::lean_inc_n(v_pre_6307_, 2);
    leanh::lean_inc_ref(v_inst_6306_);
    leanh::lean_inc(v_inst_6305_);
    leanh::lean_inc_ref(v_inst_6304_);
    v___f_6317_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7___boxed
            as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___f_6317_, 0, v_inst_6304_);
    leanh::lean_closure_set(v___f_6317_, 1, v_inst_6305_);
    leanh::lean_closure_set(v___f_6317_, 2, v_inst_6306_);
    leanh::lean_closure_set(v___f_6317_, 3, v_pre_6307_);
    leanh::lean_closure_set(v___f_6317_, 4, v_post_6308_);
    leanh::lean_closure_set(v___f_6317_, 5, v_x_6309_);
    leanh::lean_closure_set(v___f_6317_, 6, v_x_6310_);
    leanh::lean_closure_set(v___f_6317_, 7, v___y_6316_);
    leanh::lean_inc_ref(v_e_6314_);
    leanh::lean_inc(v_toBind_6312_);
    v___f_6318_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___boxed
            as *mut core::ffi::c_void,
        14,
        13,
    );
    leanh::lean_closure_set(v___f_6318_, 0, v_toApplicative_6311_);
    leanh::lean_closure_set(v___f_6318_, 1, v_inst_6304_);
    leanh::lean_closure_set(v___f_6318_, 2, v_inst_6305_);
    leanh::lean_closure_set(v___f_6318_, 3, v_inst_6306_);
    leanh::lean_closure_set(v___f_6318_, 4, v_pre_6307_);
    leanh::lean_closure_set(v___f_6318_, 5, v_post_6308_);
    leanh::lean_closure_set(v___f_6318_, 6, v_x_6309_);
    leanh::lean_closure_set(v___f_6318_, 7, v_x_6310_);
    leanh::lean_closure_set(v___f_6318_, 8, v___y_6316_);
    leanh::lean_closure_set(v___f_6318_, 9, v_toBind_6312_);
    leanh::lean_closure_set(v___f_6318_, 10, v___f_6317_);
    leanh::lean_closure_set(v___f_6318_, 11, v___f_6313_);
    leanh::lean_closure_set(v___f_6318_, 12, v_e_6314_);
    v___x_6319_ = leanh::lean_apply_1(v_pre_6307_, v_e_6314_);
    v___x_6320_ = leanh::lean_apply_4(
        v_toBind_6312_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6319_,
        v___f_6318_,
    );
    return v___x_6320_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___boxed(
    mut v_inst_6321_: *mut leanh::LeanObject,
    mut v_inst_6322_: *mut leanh::LeanObject,
    mut v_inst_6323_: *mut leanh::LeanObject,
    mut v_pre_6324_: *mut leanh::LeanObject,
    mut v_post_6325_: *mut leanh::LeanObject,
    mut v_x_6326_: *mut leanh::LeanObject,
    mut v_x_6327_: *mut leanh::LeanObject,
    mut v_toApplicative_6328_: *mut leanh::LeanObject,
    mut v_toBind_6329_: *mut leanh::LeanObject,
    mut v___f_6330_: *mut leanh::LeanObject,
    mut v_e_6331_: *mut leanh::LeanObject,
    mut v_____r_6332_: *mut leanh::LeanObject,
    mut v___y_6333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6334_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18(
        v_inst_6321_,
        v_inst_6322_,
        v_inst_6323_,
        v_pre_6324_,
        v_post_6325_,
        v_x_6326_,
        v_x_6327_,
        v_toApplicative_6328_,
        v_toBind_6329_,
        v___f_6330_,
        v_e_6331_,
        v_____r_6332_,
        v___y_6333_,
    );
    leanh::lean_dec(v___y_6333_);
    return v_res_6334_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(
    mut v_inst_6335_: *mut leanh::LeanObject,
    mut v_inst_6336_: *mut leanh::LeanObject,
    mut v_inst_6337_: *mut leanh::LeanObject,
    mut v_pre_6338_: *mut leanh::LeanObject,
    mut v_post_6339_: *mut leanh::LeanObject,
    mut v_x_6340_: *mut leanh::LeanObject,
    mut v_x_6341_: *mut leanh::LeanObject,
    mut v_e_6342_: *mut leanh::LeanObject,
    mut v_a_6343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_6351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6344_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0;
    v___x_6345_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1;
    leanh::lean_inc_ref_n(v_inst_6335_, 3);
    v___x_6346_ =
        l_Lean_MonadCacheT_instMonad___redArg(v_x_6340_, v___x_6344_, v___x_6345_, v_inst_6335_);
    v___x_6347_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_6340_, v___x_6344_, v___x_6345_);
    leanh::lean_inc_ref_n(v_inst_6337_, 3);
    leanh::lean_inc_ref(v___x_6347_);
    v___f_6348_ = leanh::lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__3 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_6348_, 0, v___x_6347_);
    leanh::lean_closure_set(v___f_6348_, 1, v_inst_6337_);
    v___f_6349_ = leanh::lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__4 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_6349_, 0, v___x_6347_);
    leanh::lean_closure_set(v___f_6349_, 1, v_inst_6337_);
    v___x_6350_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6350_, 0, v___f_6348_);
    leanh::lean_ctor_set(v___x_6350_, 1, v___f_6349_);
    v_toApplicative_6351_ = leanh::lean_ctor_get(v_inst_6335_, 0);
    leanh::lean_inc_ref_n(v_toApplicative_6351_, 4);
    v_toBind_6352_ = leanh::lean_ctor_get(v_inst_6335_, 1);
    leanh::lean_inc_n(v_toBind_6352_, 6);
    leanh::lean_inc_n(v_x_6341_, 3);
    leanh::lean_inc_n(v_a_6343_, 3);
    leanh::lean_inc_ref_n(v_e_6342_, 2);
    v___f_6353_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2___boxed
            as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_6353_, 0, v_toApplicative_6351_);
    leanh::lean_closure_set(v___f_6353_, 1, v___x_6344_);
    leanh::lean_closure_set(v___f_6353_, 2, v___x_6345_);
    leanh::lean_closure_set(v___f_6353_, 3, v_e_6342_);
    leanh::lean_closure_set(v___f_6353_, 4, v_a_6343_);
    leanh::lean_closure_set(v___f_6353_, 5, v_x_6341_);
    leanh::lean_closure_set(v___f_6353_, 6, v_toBind_6352_);
    v___f_6354_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_6354_, 0, v_toApplicative_6351_);
    leanh::lean_closure_set(v___f_6354_, 1, v___x_6344_);
    leanh::lean_closure_set(v___f_6354_, 2, v___x_6345_);
    leanh::lean_closure_set(v___f_6354_, 3, v_e_6342_);
    leanh::lean_inc_ref(v___x_6346_);
    leanh::lean_inc(v_post_6339_);
    leanh::lean_inc(v_pre_6338_);
    leanh::lean_inc_n(v_inst_6336_, 2);
    v___f_6355_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6___boxed
            as *mut core::ffi::c_void,
        12,
        9,
    );
    leanh::lean_closure_set(v___f_6355_, 0, v_inst_6335_);
    leanh::lean_closure_set(v___f_6355_, 1, v_inst_6336_);
    leanh::lean_closure_set(v___f_6355_, 2, v_inst_6337_);
    leanh::lean_closure_set(v___f_6355_, 3, v_pre_6338_);
    leanh::lean_closure_set(v___f_6355_, 4, v_post_6339_);
    leanh::lean_closure_set(v___f_6355_, 5, v_x_6340_);
    leanh::lean_closure_set(v___f_6355_, 6, v_x_6341_);
    leanh::lean_closure_set(v___f_6355_, 7, v___x_6346_);
    leanh::lean_closure_set(v___f_6355_, 8, v_toBind_6352_);
    v___f_6356_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___boxed
            as *mut core::ffi::c_void,
        13,
        11,
    );
    leanh::lean_closure_set(v___f_6356_, 0, v_inst_6335_);
    leanh::lean_closure_set(v___f_6356_, 1, v_inst_6336_);
    leanh::lean_closure_set(v___f_6356_, 2, v_inst_6337_);
    leanh::lean_closure_set(v___f_6356_, 3, v_pre_6338_);
    leanh::lean_closure_set(v___f_6356_, 4, v_post_6339_);
    leanh::lean_closure_set(v___f_6356_, 5, v_x_6340_);
    leanh::lean_closure_set(v___f_6356_, 6, v_x_6341_);
    leanh::lean_closure_set(v___f_6356_, 7, v_toApplicative_6351_);
    leanh::lean_closure_set(v___f_6356_, 8, v_toBind_6352_);
    leanh::lean_closure_set(v___f_6356_, 9, v___f_6355_);
    leanh::lean_closure_set(v___f_6356_, 10, v_e_6342_);
    v___f_6357_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___boxed
            as *mut core::ffi::c_void,
        13,
        12,
    );
    leanh::lean_closure_set(v___f_6357_, 0, v_inst_6336_);
    leanh::lean_closure_set(v___f_6357_, 1, v_x_6340_);
    leanh::lean_closure_set(v___f_6357_, 2, v___x_6344_);
    leanh::lean_closure_set(v___f_6357_, 3, v___x_6345_);
    leanh::lean_closure_set(v___f_6357_, 4, v_inst_6335_);
    leanh::lean_closure_set(v___f_6357_, 5, v___f_6356_);
    leanh::lean_closure_set(v___f_6357_, 6, v___x_6346_);
    leanh::lean_closure_set(v___f_6357_, 7, v___x_6350_);
    leanh::lean_closure_set(v___f_6357_, 8, v_a_6343_);
    leanh::lean_closure_set(v___f_6357_, 9, v_toBind_6352_);
    leanh::lean_closure_set(v___f_6357_, 10, v___f_6353_);
    leanh::lean_closure_set(v___f_6357_, 11, v_toApplicative_6351_);
    v___x_6358_ =
        leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_6358_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_6358_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_6358_, 2, v_a_6343_);
    v___x_6359_ = leanh::lean_apply_2(v_x_6341_, leanh::lean_box(0), v___x_6358_);
    v___x_6360_ = leanh::lean_apply_4(
        v_toBind_6352_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6359_,
        v___f_6354_,
    );
    v___x_6361_ = leanh::lean_apply_4(
        v_toBind_6352_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6360_,
        v___f_6357_,
    );
    return v___x_6361_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0(
    mut v_toApplicative_6362_: *mut leanh::LeanObject,
    mut v_inst_6363_: *mut leanh::LeanObject,
    mut v_inst_6364_: *mut leanh::LeanObject,
    mut v_inst_6365_: *mut leanh::LeanObject,
    mut v_pre_6366_: *mut leanh::LeanObject,
    mut v_post_6367_: *mut leanh::LeanObject,
    mut v_x_6368_: *mut leanh::LeanObject,
    mut v_x_6369_: *mut leanh::LeanObject,
    mut v_a_6370_: *mut leanh::LeanObject,
    mut v_e_6371_: *mut leanh::LeanObject,
    mut v_a_6372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_6377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_6380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_6382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_a_6372_) {
                0 => {
                    leanh::lean_dec_ref(v_e_6371_);
                    leanh::lean_dec(v_x_6369_);
                    leanh::lean_dec(v_post_6367_);
                    leanh::lean_dec(v_pre_6366_);
                    leanh::lean_dec_ref(v_inst_6365_);
                    leanh::lean_dec(v_inst_6364_);
                    leanh::lean_dec_ref(v_inst_6363_);
                    v_e_6377_ = leanh::lean_ctor_get(v_a_6372_, 0);
                    leanh::lean_inc_ref(v_e_6377_);
                    leanh::lean_dec_ref_known(v_a_6372_, 1);
                    v_toPure_6378_ = leanh::lean_ctor_get(v_toApplicative_6362_, 1);
                    leanh::lean_inc(v_toPure_6378_);
                    leanh::lean_dec_ref(v_toApplicative_6362_);
                    v___x_6379_ = leanh::lean_apply_2(
                        v_toPure_6378_,
                        leanh::lean_box(0),
                        v_e_6377_,
                    );
                    return v___x_6379_;
                }
                1 => {
                    leanh::lean_dec_ref(v_e_6371_);
                    leanh::lean_dec_ref(v_toApplicative_6362_);
                    v_e_6380_ = leanh::lean_ctor_get(v_a_6372_, 0);
                    leanh::lean_inc_ref(v_e_6380_);
                    leanh::lean_dec_ref_known(v_a_6372_, 1);
                    v___x_6381_ =
                        l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(
                            v_inst_6363_,
                            v_inst_6364_,
                            v_inst_6365_,
                            v_pre_6366_,
                            v_post_6367_,
                            v_x_6368_,
                            v_x_6369_,
                            v_e_6380_,
                            v_a_6370_,
                        );
                    return v___x_6381_;
                }
                _ => {
                    leanh::lean_dec(v_x_6369_);
                    leanh::lean_dec(v_post_6367_);
                    leanh::lean_dec(v_pre_6366_);
                    leanh::lean_dec_ref(v_inst_6365_);
                    leanh::lean_dec(v_inst_6364_);
                    leanh::lean_dec_ref(v_inst_6363_);
                    v_e_x3f_6382_ = leanh::lean_ctor_get(v_a_6372_, 0);
                    leanh::lean_inc(v_e_x3f_6382_);
                    leanh::lean_dec_ref_known(v_a_6372_, 1);
                    if leanh::lean_obj_tag(v_e_x3f_6382_) == 0 {
                        v___y_6374_ = v_e_6371_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_e_6371_);
                        v_val_6383_ = leanh::lean_ctor_get(v_e_x3f_6382_, 0);
                        leanh::lean_inc(v_val_6383_);
                        leanh::lean_dec_ref_known(v_e_x3f_6382_, 1);
                        v___y_6374_ = v_val_6383_;
                        state = 1;
                        continue;
                    }
                }
            },
            1 => {
                v_toPure_6375_ = leanh::lean_ctor_get(v_toApplicative_6362_, 1);
                leanh::lean_inc(v_toPure_6375_);
                leanh::lean_dec_ref(v_toApplicative_6362_);
                v___x_6376_ = leanh::lean_apply_2(
                    v_toPure_6375_,
                    leanh::lean_box(0),
                    v___y_6374_,
                );
                return v___x_6376_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0___boxed(
    mut v_toApplicative_6384_: *mut leanh::LeanObject,
    mut v_inst_6385_: *mut leanh::LeanObject,
    mut v_inst_6386_: *mut leanh::LeanObject,
    mut v_inst_6387_: *mut leanh::LeanObject,
    mut v_pre_6388_: *mut leanh::LeanObject,
    mut v_post_6389_: *mut leanh::LeanObject,
    mut v_x_6390_: *mut leanh::LeanObject,
    mut v_x_6391_: *mut leanh::LeanObject,
    mut v_a_6392_: *mut leanh::LeanObject,
    mut v_e_6393_: *mut leanh::LeanObject,
    mut v_a_6394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6395_ =
        l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0(
            v_toApplicative_6384_,
            v_inst_6385_,
            v_inst_6386_,
            v_inst_6387_,
            v_pre_6388_,
            v_post_6389_,
            v_x_6390_,
            v_x_6391_,
            v_a_6392_,
            v_e_6393_,
            v_a_6394_,
        );
    leanh::lean_dec(v_a_6392_);
    return v_res_6395_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(
    mut v_inst_6396_: *mut leanh::LeanObject,
    mut v_inst_6397_: *mut leanh::LeanObject,
    mut v_inst_6398_: *mut leanh::LeanObject,
    mut v_pre_6399_: *mut leanh::LeanObject,
    mut v_post_6400_: *mut leanh::LeanObject,
    mut v_x_6401_: *mut leanh::LeanObject,
    mut v_x_6402_: *mut leanh::LeanObject,
    mut v_e_6403_: *mut leanh::LeanObject,
    mut v_a_6404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_6405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6405_ = leanh::lean_ctor_get(v_inst_6396_, 0);
    leanh::lean_inc_ref(v_toApplicative_6405_);
    v_toBind_6406_ = leanh::lean_ctor_get(v_inst_6396_, 1);
    leanh::lean_inc(v_toBind_6406_);
    leanh::lean_inc_ref(v_e_6403_);
    leanh::lean_inc(v_a_6404_);
    leanh::lean_inc(v_post_6400_);
    v___f_6407_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 10);
    leanh::lean_closure_set(v___f_6407_, 0, v_toApplicative_6405_);
    leanh::lean_closure_set(v___f_6407_, 1, v_inst_6396_);
    leanh::lean_closure_set(v___f_6407_, 2, v_inst_6397_);
    leanh::lean_closure_set(v___f_6407_, 3, v_inst_6398_);
    leanh::lean_closure_set(v___f_6407_, 4, v_pre_6399_);
    leanh::lean_closure_set(v___f_6407_, 5, v_post_6400_);
    leanh::lean_closure_set(v___f_6407_, 6, v_x_6401_);
    leanh::lean_closure_set(v___f_6407_, 7, v_x_6402_);
    leanh::lean_closure_set(v___f_6407_, 8, v_a_6404_);
    leanh::lean_closure_set(v___f_6407_, 9, v_e_6403_);
    v___x_6408_ = leanh::lean_apply_1(v_post_6400_, v_e_6403_);
    v___x_6409_ = leanh::lean_apply_4(
        v_toBind_6406_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6408_,
        v___f_6407_,
    );
    return v___x_6409_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7(
    mut v_inst_6410_: *mut leanh::LeanObject,
    mut v_inst_6411_: *mut leanh::LeanObject,
    mut v_inst_6412_: *mut leanh::LeanObject,
    mut v_pre_6413_: *mut leanh::LeanObject,
    mut v_post_6414_: *mut leanh::LeanObject,
    mut v_x_6415_: *mut leanh::LeanObject,
    mut v_x_6416_: *mut leanh::LeanObject,
    mut v___y_6417_: *mut leanh::LeanObject,
    mut v_a_6418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6419_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(
        v_inst_6410_,
        v_inst_6411_,
        v_inst_6412_,
        v_pre_6413_,
        v_post_6414_,
        v_x_6415_,
        v_x_6416_,
        v_a_6418_,
        v___y_6417_,
    );
    return v___x_6419_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___boxed(
    mut v_inst_6420_: *mut leanh::LeanObject,
    mut v_inst_6421_: *mut leanh::LeanObject,
    mut v_inst_6422_: *mut leanh::LeanObject,
    mut v_pre_6423_: *mut leanh::LeanObject,
    mut v_post_6424_: *mut leanh::LeanObject,
    mut v_x_6425_: *mut leanh::LeanObject,
    mut v_x_6426_: *mut leanh::LeanObject,
    mut v_e_6427_: *mut leanh::LeanObject,
    mut v_a_6428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6429_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(
        v_inst_6420_,
        v_inst_6421_,
        v_inst_6422_,
        v_pre_6423_,
        v_post_6424_,
        v_x_6425_,
        v_x_6426_,
        v_e_6427_,
        v_a_6428_,
    );
    leanh::lean_dec(v_a_6428_);
    return v_res_6429_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit(
    mut v_m_6430_: *mut leanh::LeanObject,
    mut v_inst_6431_: *mut leanh::LeanObject,
    mut v_inst_6432_: *mut leanh::LeanObject,
    mut v_inst_6433_: *mut leanh::LeanObject,
    mut v_pre_6434_: *mut leanh::LeanObject,
    mut v_post_6435_: *mut leanh::LeanObject,
    mut v_x_6436_: *mut leanh::LeanObject,
    mut v_x_6437_: *mut leanh::LeanObject,
    mut v_e_6438_: *mut leanh::LeanObject,
    mut v_a_6439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6440_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(
        v_inst_6431_,
        v_inst_6432_,
        v_inst_6433_,
        v_pre_6434_,
        v_post_6435_,
        v_x_6436_,
        v_x_6437_,
        v_e_6438_,
        v_a_6439_,
    );
    return v___x_6440_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___boxed(
    mut v_m_6441_: *mut leanh::LeanObject,
    mut v_inst_6442_: *mut leanh::LeanObject,
    mut v_inst_6443_: *mut leanh::LeanObject,
    mut v_inst_6444_: *mut leanh::LeanObject,
    mut v_pre_6445_: *mut leanh::LeanObject,
    mut v_post_6446_: *mut leanh::LeanObject,
    mut v_x_6447_: *mut leanh::LeanObject,
    mut v_x_6448_: *mut leanh::LeanObject,
    mut v_e_6449_: *mut leanh::LeanObject,
    mut v_a_6450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6451_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit(
        v_m_6441_,
        v_inst_6442_,
        v_inst_6443_,
        v_inst_6444_,
        v_pre_6445_,
        v_post_6446_,
        v_x_6447_,
        v_x_6448_,
        v_e_6449_,
        v_a_6450_,
    );
    leanh::lean_dec(v_a_6450_);
    return v_res_6451_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost(
    mut v_m_6452_: *mut leanh::LeanObject,
    mut v_inst_6453_: *mut leanh::LeanObject,
    mut v_inst_6454_: *mut leanh::LeanObject,
    mut v_inst_6455_: *mut leanh::LeanObject,
    mut v_pre_6456_: *mut leanh::LeanObject,
    mut v_post_6457_: *mut leanh::LeanObject,
    mut v_x_6458_: *mut leanh::LeanObject,
    mut v_x_6459_: *mut leanh::LeanObject,
    mut v_e_6460_: *mut leanh::LeanObject,
    mut v_a_6461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6462_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(
        v_inst_6453_,
        v_inst_6454_,
        v_inst_6455_,
        v_pre_6456_,
        v_post_6457_,
        v_x_6458_,
        v_x_6459_,
        v_e_6460_,
        v_a_6461_,
    );
    return v___x_6462_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___boxed(
    mut v_m_6463_: *mut leanh::LeanObject,
    mut v_inst_6464_: *mut leanh::LeanObject,
    mut v_inst_6465_: *mut leanh::LeanObject,
    mut v_inst_6466_: *mut leanh::LeanObject,
    mut v_pre_6467_: *mut leanh::LeanObject,
    mut v_post_6468_: *mut leanh::LeanObject,
    mut v_x_6469_: *mut leanh::LeanObject,
    mut v_x_6470_: *mut leanh::LeanObject,
    mut v_e_6471_: *mut leanh::LeanObject,
    mut v_a_6472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6473_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost(
        v_m_6463_,
        v_inst_6464_,
        v_inst_6465_,
        v_inst_6466_,
        v_pre_6467_,
        v_post_6468_,
        v_x_6469_,
        v_x_6470_,
        v_e_6471_,
        v_a_6472_,
    );
    leanh::lean_dec(v_a_6472_);
    return v_res_6473_;
}
pub unsafe fn l_Lean_Core_transform___redArg___lam__0(
    mut v_x_6474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6476_ = leanh::lean_apply_1(v_x_6474_, leanh::lean_box(0));
    v___x_6477_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6477_, 0, v___x_6476_);
    return v___x_6477_;
}
pub unsafe fn l_Lean_Core_transform___redArg___lam__0___boxed(
    mut v_x_6478_: *mut leanh::LeanObject,
    mut v___y_6479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6480_ = l_Lean_Core_transform___redArg___lam__0(v_x_6478_);
    return v_res_6480_;
}
pub unsafe fn l_Lean_Core_transform___redArg___lam__1(
    mut v_inst_6481_: *mut leanh::LeanObject,
    mut v_00_u03b1_6482_: *mut leanh::LeanObject,
    mut v_x_6483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6484_ = leanh::lean_alloc_closure(
        l_Lean_Core_transform___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_6484_, 0, v_x_6483_);
    v___x_6485_ = leanh::lean_alloc_closure(
        l_Lean_Core_liftIOCore___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___x_6485_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_6485_, 1, v___f_6484_);
    v___x_6486_ = leanh::lean_apply_2(v_inst_6481_, leanh::lean_box(0), v___x_6485_);
    return v___x_6486_;
}
pub unsafe fn l_Lean_Core_transform___redArg___lam__2(
    mut v_toPure_6487_: *mut leanh::LeanObject,
    mut v_____x_6488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_6489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_6489_ = leanh::lean_ctor_get(v_____x_6488_, 0);
    leanh::lean_inc(v_fst_6489_);
    leanh::lean_dec_ref(v_____x_6488_);
    v___x_6490_ =
        leanh::lean_apply_2(v_toPure_6487_, leanh::lean_box(0), v_fst_6489_);
    return v___x_6490_;
}
pub unsafe fn l_Lean_Core_transform___redArg___lam__3(
    mut v_a_6491_: *mut leanh::LeanObject,
    mut v_toPure_6492_: *mut leanh::LeanObject,
    mut v_s_6493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6494_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6494_, 0, v_a_6491_);
    leanh::lean_ctor_set(v___x_6494_, 1, v_s_6493_);
    v___x_6495_ =
        leanh::lean_apply_2(v_toPure_6492_, leanh::lean_box(0), v___x_6494_);
    return v___x_6495_;
}
pub unsafe fn l_Lean_Core_transform___redArg___lam__4(
    mut v_toPure_6496_: *mut leanh::LeanObject,
    mut v_ref_6497_: *mut leanh::LeanObject,
    mut v_x_6498_: *mut leanh::LeanObject,
    mut v_toBind_6499_: *mut leanh::LeanObject,
    mut v_a_6500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6501_ = leanh::lean_alloc_closure(
        l_Lean_Core_transform___redArg___lam__3 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_6501_, 0, v_a_6500_);
    leanh::lean_closure_set(v___f_6501_, 1, v_toPure_6496_);
    v___x_6502_ =
        leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_6502_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_6502_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_6502_, 2, v_ref_6497_);
    v___x_6503_ = leanh::lean_apply_2(v_x_6498_, leanh::lean_box(0), v___x_6502_);
    v___x_6504_ = leanh::lean_apply_4(
        v_toBind_6499_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6503_,
        v___f_6501_,
    );
    return v___x_6504_;
}
pub unsafe fn l_Lean_Core_transform___redArg___lam__5(
    mut v_toPure_6505_: *mut leanh::LeanObject,
    mut v_x_6506_: *mut leanh::LeanObject,
    mut v_toBind_6507_: *mut leanh::LeanObject,
    mut v_inst_6508_: *mut leanh::LeanObject,
    mut v_inst_6509_: *mut leanh::LeanObject,
    mut v_inst_6510_: *mut leanh::LeanObject,
    mut v_pre_6511_: *mut leanh::LeanObject,
    mut v_post_6512_: *mut leanh::LeanObject,
    mut v_x_6513_: *mut leanh::LeanObject,
    mut v_input_6514_: *mut leanh::LeanObject,
    mut v_ref_6515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6518_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_6507_);
    leanh::lean_inc(v_x_6506_);
    leanh::lean_inc(v_ref_6515_);
    v___f_6516_ = leanh::lean_alloc_closure(
        l_Lean_Core_transform___redArg___lam__4 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_6516_, 0, v_toPure_6505_);
    leanh::lean_closure_set(v___f_6516_, 1, v_ref_6515_);
    leanh::lean_closure_set(v___f_6516_, 2, v_x_6506_);
    leanh::lean_closure_set(v___f_6516_, 3, v_toBind_6507_);
    v___x_6517_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(
        v_inst_6508_,
        v_inst_6509_,
        v_inst_6510_,
        v_pre_6511_,
        v_post_6512_,
        v_x_6513_,
        v_x_6506_,
        v_input_6514_,
        v_ref_6515_,
    );
    leanh::lean_dec(v_ref_6515_);
    v___x_6518_ = leanh::lean_apply_4(
        v_toBind_6507_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6517_,
        v___f_6516_,
    );
    return v___x_6518_;
}
pub unsafe fn _init_l_Lean_Core_transform___redArg___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_6519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6519_ = leanh::lean_box(0);
    v___x_6520_ = leanh::lean_unsigned_to_nat(16);
    v___x_6521_ = lean_mk_array(v___x_6520_, v___x_6519_);
    return v___x_6521_;
}
pub unsafe fn _init_l_Lean_Core_transform___redArg___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_6522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6522_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Core_transform___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Core_transform___redArg___closed__0_once),
        _init_l_Lean_Core_transform___redArg___closed__0,
    );
    v___x_6523_ = leanh::lean_unsigned_to_nat(0);
    v___x_6524_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6524_, 0, v___x_6523_);
    leanh::lean_ctor_set(v___x_6524_, 1, v___x_6522_);
    return v___x_6524_;
}
pub unsafe fn _init_l_Lean_Core_transform___redArg___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_6525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6525_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Core_transform___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Core_transform___redArg___closed__1_once),
        _init_l_Lean_Core_transform___redArg___closed__1,
    );
    v___x_6526_ =
        leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_6526_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_6526_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_6526_, 2, v___x_6525_);
    return v___x_6526_;
}
pub unsafe fn l_Lean_Core_transform___redArg(
    mut v_inst_6527_: *mut leanh::LeanObject,
    mut v_inst_6528_: *mut leanh::LeanObject,
    mut v_inst_6529_: *mut leanh::LeanObject,
    mut v_input_6530_: *mut leanh::LeanObject,
    mut v_pre_6531_: *mut leanh::LeanObject,
    mut v_post_6532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_6533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_6534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_6537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_6533_ = leanh::lean_box(0);
    v_toApplicative_6534_ = leanh::lean_ctor_get(v_inst_6527_, 0);
    v_toBind_6535_ = leanh::lean_ctor_get(v_inst_6527_, 1);
    leanh::lean_inc_n(v_toBind_6535_, 3);
    v_toPure_6536_ = leanh::lean_ctor_get(v_toApplicative_6534_, 1);
    leanh::lean_inc_n(v_toPure_6536_, 2);
    leanh::lean_inc_n(v_inst_6528_, 2);
    v_x_6537_ = leanh::lean_alloc_closure(
        l_Lean_Core_transform___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v_x_6537_, 0, v_inst_6528_);
    v___x_6538_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Core_transform___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Core_transform___redArg___closed__2_once),
        _init_l_Lean_Core_transform___redArg___closed__2,
    );
    v___x_6539_ = l_Lean_Core_transform___redArg___lam__1(
        v_inst_6528_,
        leanh::lean_box(0),
        v___x_6538_,
    );
    v___f_6540_ = leanh::lean_alloc_closure(
        l_Lean_Core_transform___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_6540_, 0, v_toPure_6536_);
    v___f_6541_ = leanh::lean_alloc_closure(
        l_Lean_Core_transform___redArg___lam__5 as *mut core::ffi::c_void,
        11,
        10,
    );
    leanh::lean_closure_set(v___f_6541_, 0, v_toPure_6536_);
    leanh::lean_closure_set(v___f_6541_, 1, v_x_6537_);
    leanh::lean_closure_set(v___f_6541_, 2, v_toBind_6535_);
    leanh::lean_closure_set(v___f_6541_, 3, v_inst_6527_);
    leanh::lean_closure_set(v___f_6541_, 4, v_inst_6528_);
    leanh::lean_closure_set(v___f_6541_, 5, v_inst_6529_);
    leanh::lean_closure_set(v___f_6541_, 6, v_pre_6531_);
    leanh::lean_closure_set(v___f_6541_, 7, v_post_6532_);
    leanh::lean_closure_set(v___f_6541_, 8, v_x_6533_);
    leanh::lean_closure_set(v___f_6541_, 9, v_input_6530_);
    v___x_6542_ = leanh::lean_apply_4(
        v_toBind_6535_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6539_,
        v___f_6541_,
    );
    v___x_6543_ = leanh::lean_apply_4(
        v_toBind_6535_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6542_,
        v___f_6540_,
    );
    return v___x_6543_;
}
pub unsafe fn l_Lean_Core_transform(
    mut v_m_6544_: *mut leanh::LeanObject,
    mut v_inst_6545_: *mut leanh::LeanObject,
    mut v_inst_6546_: *mut leanh::LeanObject,
    mut v_inst_6547_: *mut leanh::LeanObject,
    mut v_input_6548_: *mut leanh::LeanObject,
    mut v_pre_6549_: *mut leanh::LeanObject,
    mut v_post_6550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6551_ = l_Lean_Core_transform___redArg(
        v_inst_6545_,
        v_inst_6546_,
        v_inst_6547_,
        v_input_6548_,
        v_pre_6549_,
        v_post_6550_,
    );
    return v___x_6551_;
}
pub unsafe fn l_Lean_Core_betaReduce___lam__0(
    mut v_e_6554_: *mut leanh::LeanObject,
    mut v___y_6555_: *mut leanh::LeanObject,
    mut v___y_6556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6558_: u8 = 0;
    let mut v___x_6559_: u8 = 0;
    v___x_6558_ = 0;
    v___x_6559_ = l_Lean_Expr_isHeadBetaTarget(v_e_6554_, v___x_6558_);
    if v___x_6559_ == 0 {
        let mut v___x_6560_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6561_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_e_6554_);
        v___x_6560_ = l_Lean_Core_betaReduce___lam__0___closed__0;
        v___x_6561_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6561_, 0, v___x_6560_);
        return v___x_6561_;
    } else {
        let mut v___x_6562_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6563_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6564_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6562_ = l_Lean_Expr_headBeta(v_e_6554_);
        v___x_6563_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6563_, 0, v___x_6562_);
        v___x_6564_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6564_, 0, v___x_6563_);
        return v___x_6564_;
    }
}
pub unsafe fn l_Lean_Core_betaReduce___lam__0___boxed(
    mut v_e_6565_: *mut leanh::LeanObject,
    mut v___y_6566_: *mut leanh::LeanObject,
    mut v___y_6567_: *mut leanh::LeanObject,
    mut v___y_6568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6569_ = l_Lean_Core_betaReduce___lam__0(v_e_6565_, v___y_6566_, v___y_6567_);
    leanh::lean_dec(v___y_6567_);
    leanh::lean_dec_ref(v___y_6566_);
    return v_res_6569_;
}
pub unsafe fn l_Lean_Core_betaReduce___lam__1(
    mut v_e_6570_: *mut leanh::LeanObject,
    mut v___y_6571_: *mut leanh::LeanObject,
    mut v___y_6572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6574_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6574_, 0, v_e_6570_);
    v___x_6575_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6575_, 0, v___x_6574_);
    return v___x_6575_;
}
pub unsafe fn l_Lean_Core_betaReduce___lam__1___boxed(
    mut v_e_6576_: *mut leanh::LeanObject,
    mut v___y_6577_: *mut leanh::LeanObject,
    mut v___y_6578_: *mut leanh::LeanObject,
    mut v___y_6579_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6580_ = l_Lean_Core_betaReduce___lam__1(v_e_6576_, v___y_6577_, v___y_6578_);
    leanh::lean_dec(v___y_6578_);
    leanh::lean_dec_ref(v___y_6577_);
    return v_res_6580_;
}
pub unsafe fn _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_6581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6581_ = leanh::lean_box(0);
    v___x_6582_ = l_Lean_interruptExceptionId;
    v___x_6583_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6583_, 0, v___x_6582_);
    leanh::lean_ctor_set(v___x_6583_, 1, v___x_6581_);
    return v___x_6583_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_6585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6585_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once), _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
    v___x_6586_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6586_, 0, v___x_6585_);
    return v___x_6586_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___boxed(
    mut v___y_6587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6588_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
    return v_res_6588_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_6594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6594_ = l_Lean_maxRecDepthErrorMessage;
    v___x_6595_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6595_, 0, v___x_6594_);
    return v___x_6595_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_6596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6596_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
    v___x_6597_ = l_Lean_MessageData_ofFormat(v___x_6596_);
    return v___x_6597_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_6598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6598_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
    v___x_6599_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__2;
    v___x_6600_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6600_, 0, v___x_6599_);
    leanh::lean_ctor_set(v___x_6600_, 1, v___x_6598_);
    return v___x_6600_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(
    mut v_ref_6601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6603_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
    v___x_6604_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6604_, 0, v_ref_6601_);
    leanh::lean_ctor_set(v___x_6604_, 1, v___x_6603_);
    v___x_6605_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6605_, 0, v___x_6604_);
    return v___x_6605_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___boxed(
    mut v_ref_6606_: *mut leanh::LeanObject,
    mut v___y_6607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6608_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_6606_);
    return v_res_6608_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(
    mut v_x_6609_: *mut leanh::LeanObject,
    mut v___y_6610_: *mut leanh::LeanObject,
    mut v___y_6611_: *mut leanh::LeanObject,
    mut v___y_6612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6619_: u8 = 0;
    let mut v___x_6621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6623_: u8 = 0;
    let mut v___y_6625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6628_: u8 = 0;
    let mut v___y_6629_: u8 = 0;
    let mut v___y_6630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_6645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_6653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_6654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6657_: u8 = 0;
    let mut v_cancelTk_x3f_6658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6659_: u8 = 0;
    let mut v_inheritedTraceOptions_6660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6663_: u8 = 0;
    let mut v___x_6664_: u8 = 0;
    let mut v___x_6665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6667_: u8 = 0;
    let mut v___x_6668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6672_: u8 = 0;
    let mut v___x_6674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6676_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_6645_ = leanh::lean_ctor_get(v___y_6611_, 0);
                v_fileMap_6646_ = leanh::lean_ctor_get(v___y_6611_, 1);
                v_options_6647_ = leanh::lean_ctor_get(v___y_6611_, 2);
                v_currRecDepth_6648_ = leanh::lean_ctor_get(v___y_6611_, 3);
                v_maxRecDepth_6649_ = leanh::lean_ctor_get(v___y_6611_, 4);
                v_ref_6650_ = leanh::lean_ctor_get(v___y_6611_, 5);
                v_currNamespace_6651_ = leanh::lean_ctor_get(v___y_6611_, 6);
                v_openDecls_6652_ = leanh::lean_ctor_get(v___y_6611_, 7);
                v_initHeartbeats_6653_ = leanh::lean_ctor_get(v___y_6611_, 8);
                v_maxHeartbeats_6654_ = leanh::lean_ctor_get(v___y_6611_, 9);
                v_quotContext_6655_ = leanh::lean_ctor_get(v___y_6611_, 10);
                v_currMacroScope_6656_ = leanh::lean_ctor_get(v___y_6611_, 11);
                v_diag_6657_ = leanh::lean_ctor_get_uint8(
                    v___y_6611_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_6658_ = leanh::lean_ctor_get(v___y_6611_, 12);
                v_suppressElabErrors_6659_ = leanh::lean_ctor_get_uint8(
                    v___y_6611_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_6660_ = leanh::lean_ctor_get(v___y_6611_, 13);
                if leanh::lean_obj_tag(v_cancelTk_x3f_6658_) == 1 {
                    v_val_6666_ = leanh::lean_ctor_get(v_cancelTk_x3f_6658_, 0);
                    v___x_6667_ = l_IO_CancelToken_isSet(v_val_6666_);
                    if v___x_6667_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_x_6609_);
                        v___x_6668_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
                        v_a_6669_ = leanh::lean_ctor_get(v___x_6668_, 0);
                        v_isSharedCheck_6676_ =
                            (!leanh::lean_is_exclusive(v___x_6668_)) as u8;
                        if v_isSharedCheck_6676_ == 0 {
                            v___x_6671_ = v___x_6668_;
                            v_isShared_6672_ = v_isSharedCheck_6676_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6669_);
                            leanh::lean_dec(v___x_6668_);
                            v___x_6671_ = leanh::lean_box(0);
                            v_isShared_6672_ = v_isSharedCheck_6676_;
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
                if leanh::lean_obj_tag(v___y_6615_) == 0 {
                    return v___y_6615_;
                } else {
                    v_a_6616_ = leanh::lean_ctor_get(v___y_6615_, 0);
                    v_isSharedCheck_6623_ = (!leanh::lean_is_exclusive(v___y_6615_)) as u8;
                    if v_isSharedCheck_6623_ == 0 {
                        v___x_6618_ = v___y_6615_;
                        v_isShared_6619_ = v_isSharedCheck_6623_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6616_);
                        leanh::lean_dec(v___y_6615_);
                        v___x_6618_ = leanh::lean_box(0);
                        v_isShared_6619_ = v_isSharedCheck_6623_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6619_ == 0 {
                    v___x_6621_ = v___x_6618_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6622_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6622_, 0, v_a_6616_);
                    v___x_6621_ = v_reuseFailAlloc_6622_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6621_;
            }
            4 => {
                v___x_6641_ = leanh::lean_unsigned_to_nat(1);
                v___x_6642_ = lean_nat_add(v___y_6626_, v___x_6641_);
                leanh::lean_inc_ref(v___y_6625_);
                leanh::lean_inc(v___y_6640_);
                leanh::lean_inc(v___y_6639_);
                leanh::lean_inc(v___y_6637_);
                leanh::lean_inc(v___y_6636_);
                leanh::lean_inc(v___y_6638_);
                leanh::lean_inc(v___y_6635_);
                leanh::lean_inc(v___y_6633_);
                leanh::lean_inc(v___y_6631_);
                leanh::lean_inc_ref(v___y_6627_);
                leanh::lean_inc_ref(v___y_6634_);
                leanh::lean_inc_ref(v___y_6632_);
                v___x_6643_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_6643_, 0, v___y_6632_);
                leanh::lean_ctor_set(v___x_6643_, 1, v___y_6634_);
                leanh::lean_ctor_set(v___x_6643_, 2, v___y_6627_);
                leanh::lean_ctor_set(v___x_6643_, 3, v___x_6642_);
                leanh::lean_ctor_set(v___x_6643_, 4, v___y_6631_);
                leanh::lean_ctor_set(v___x_6643_, 5, v___y_6630_);
                leanh::lean_ctor_set(v___x_6643_, 6, v___y_6633_);
                leanh::lean_ctor_set(v___x_6643_, 7, v___y_6635_);
                leanh::lean_ctor_set(v___x_6643_, 8, v___y_6638_);
                leanh::lean_ctor_set(v___x_6643_, 9, v___y_6636_);
                leanh::lean_ctor_set(v___x_6643_, 10, v___y_6637_);
                leanh::lean_ctor_set(v___x_6643_, 11, v___y_6639_);
                leanh::lean_ctor_set(v___x_6643_, 12, v___y_6640_);
                leanh::lean_ctor_set(v___x_6643_, 13, v___y_6625_);
                leanh::lean_ctor_set_uint8(
                    v___x_6643_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v___y_6628_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6643_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v___y_6629_,
                );
                leanh::lean_inc(v___y_6612_);
                leanh::lean_inc(v___y_6610_);
                v___x_6644_ = leanh::lean_apply_4(
                    v_x_6609_,
                    v___y_6610_,
                    v___x_6643_,
                    v___y_6612_,
                    leanh::lean_box(0),
                );
                v___y_6615_ = v___x_6644_;
                state = 1;
                continue;
            }
            5 => {
                v___x_6662_ = leanh::lean_unsigned_to_nat(0);
                v___x_6663_ = lean_nat_dec_eq(v_maxRecDepth_6649_, v___x_6662_);
                if v___x_6663_ == 0 {
                    v___x_6664_ = lean_nat_dec_eq(v_currRecDepth_6648_, v_maxRecDepth_6649_);
                    if v___x_6664_ == 0 {
                        leanh::lean_inc(v_ref_6650_);
                        v___y_6625_ = v_inheritedTraceOptions_6660_;
                        v___y_6626_ = v_currRecDepth_6648_;
                        v___y_6627_ = v_options_6647_;
                        v___y_6628_ = v_diag_6657_;
                        v___y_6629_ = v_suppressElabErrors_6659_;
                        v___y_6630_ = v_ref_6650_;
                        v___y_6631_ = v_maxRecDepth_6649_;
                        v___y_6632_ = v_fileName_6645_;
                        v___y_6633_ = v_currNamespace_6651_;
                        v___y_6634_ = v_fileMap_6646_;
                        v___y_6635_ = v_openDecls_6652_;
                        v___y_6636_ = v_maxHeartbeats_6654_;
                        v___y_6637_ = v_quotContext_6655_;
                        v___y_6638_ = v_initHeartbeats_6653_;
                        v___y_6639_ = v_currMacroScope_6656_;
                        v___y_6640_ = v_cancelTk_x3f_6658_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_x_6609_);
                        leanh::lean_inc(v_ref_6650_);
                        v___x_6665_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_6650_);
                        v___y_6615_ = v___x_6665_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_ref_6650_);
                    v___y_6625_ = v_inheritedTraceOptions_6660_;
                    v___y_6626_ = v_currRecDepth_6648_;
                    v___y_6627_ = v_options_6647_;
                    v___y_6628_ = v_diag_6657_;
                    v___y_6629_ = v_suppressElabErrors_6659_;
                    v___y_6630_ = v_ref_6650_;
                    v___y_6631_ = v_maxRecDepth_6649_;
                    v___y_6632_ = v_fileName_6645_;
                    v___y_6633_ = v_currNamespace_6651_;
                    v___y_6634_ = v_fileMap_6646_;
                    v___y_6635_ = v_openDecls_6652_;
                    v___y_6636_ = v_maxHeartbeats_6654_;
                    v___y_6637_ = v_quotContext_6655_;
                    v___y_6638_ = v_initHeartbeats_6653_;
                    v___y_6639_ = v_currMacroScope_6656_;
                    v___y_6640_ = v_cancelTk_x3f_6658_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                if v_isShared_6672_ == 0 {
                    v___x_6674_ = v___x_6671_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6675_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6675_, 0, v_a_6669_);
                    v___x_6674_ = v_reuseFailAlloc_6675_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6674_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg___boxed(
    mut v_x_6677_: *mut leanh::LeanObject,
    mut v___y_6678_: *mut leanh::LeanObject,
    mut v___y_6679_: *mut leanh::LeanObject,
    mut v___y_6680_: *mut leanh::LeanObject,
    mut v___y_6681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6682_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v_x_6677_, v___y_6678_, v___y_6679_, v___y_6680_);
    leanh::lean_dec(v___y_6680_);
    leanh::lean_dec_ref(v___y_6679_);
    leanh::lean_dec(v___y_6678_);
    return v_res_6682_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(
    mut v_00_u03b1_6683_: *mut leanh::LeanObject,
    mut v_x_6684_: *mut leanh::LeanObject,
    mut v___y_6685_: *mut leanh::LeanObject,
    mut v___y_6686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6688_ = leanh::lean_apply_1(v_x_6684_, leanh::lean_box(0));
    v___x_6689_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6689_, 0, v___x_6688_);
    return v___x_6689_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0___boxed(
    mut v_00_u03b1_6690_: *mut leanh::LeanObject,
    mut v_x_6691_: *mut leanh::LeanObject,
    mut v___y_6692_: *mut leanh::LeanObject,
    mut v___y_6693_: *mut leanh::LeanObject,
    mut v___y_6694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6695_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(v_00_u03b1_6690_, v_x_6691_, v___y_6692_, v___y_6693_);
    leanh::lean_dec(v___y_6693_);
    leanh::lean_dec_ref(v___y_6692_);
    return v_res_6695_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(
    mut v_a_6696_: *mut leanh::LeanObject,
    mut v_x_6697_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6698_: u8 = 0;
    let mut v_key_6699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6701_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6697_) == 0 {
                    v___x_6698_ = 0;
                    return v___x_6698_;
                } else {
                    v_key_6699_ = leanh::lean_ctor_get(v_x_6697_, 0);
                    v_tail_6700_ = leanh::lean_ctor_get(v_x_6697_, 2);
                    v___x_6701_ = l_Lean_ExprStructEq_beq(v_key_6699_, v_a_6696_);
                    if v___x_6701_ == 0 {
                        v_x_6697_ = v_tail_6700_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6701_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg___boxed(
    mut v_a_6703_: *mut leanh::LeanObject,
    mut v_x_6704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6705_: u8 = 0;
    let mut v_r_6706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6705_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_6703_, v_x_6704_);
    leanh::lean_dec(v_x_6704_);
    leanh::lean_dec_ref(v_a_6703_);
    v_r_6706_ = leanh::lean_box((v_res_6705_) as usize);
    return v_r_6706_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(
    mut v_x_6707_: *mut leanh::LeanObject,
    mut v_x_6708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_6709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6714_: u8 = 0;
    let mut v___x_6715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6716_: u64 = 0;
    let mut v___x_6717_: u64 = 0;
    let mut v___x_6718_: u64 = 0;
    let mut v_fold_6719_: u64 = 0;
    let mut v___x_6720_: u64 = 0;
    let mut v___x_6721_: u64 = 0;
    let mut v___x_6722_: u64 = 0;
    let mut v___x_6723_: usize = 0;
    let mut v___x_6724_: usize = 0;
    let mut v___x_6725_: usize = 0;
    let mut v___x_6726_: usize = 0;
    let mut v___x_6727_: usize = 0;
    let mut v___x_6728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6734_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6708_) == 0 {
                    return v_x_6707_;
                } else {
                    v_key_6709_ = leanh::lean_ctor_get(v_x_6708_, 0);
                    v_value_6710_ = leanh::lean_ctor_get(v_x_6708_, 1);
                    v_tail_6711_ = leanh::lean_ctor_get(v_x_6708_, 2);
                    v_isSharedCheck_6734_ = (!leanh::lean_is_exclusive(v_x_6708_)) as u8;
                    if v_isSharedCheck_6734_ == 0 {
                        v___x_6713_ = v_x_6708_;
                        v_isShared_6714_ = v_isSharedCheck_6734_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_6711_);
                        leanh::lean_inc(v_value_6710_);
                        leanh::lean_inc(v_key_6709_);
                        leanh::lean_dec(v_x_6708_);
                        v___x_6713_ = leanh::lean_box(0);
                        v_isShared_6714_ = v_isSharedCheck_6734_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6715_ = lean_array_get_size(v_x_6707_);
                v___x_6716_ = l_Lean_ExprStructEq_hash(v_key_6709_);
                v___x_6717_ = 32u64;
                v___x_6718_ = lean_uint64_shift_right(v___x_6716_, v___x_6717_);
                v_fold_6719_ = lean_uint64_xor(v___x_6716_, v___x_6718_);
                v___x_6720_ = 16u64;
                v___x_6721_ = lean_uint64_shift_right(v_fold_6719_, v___x_6720_);
                v___x_6722_ = lean_uint64_xor(v_fold_6719_, v___x_6721_);
                v___x_6723_ = lean_uint64_to_usize(v___x_6722_);
                v___x_6724_ = lean_usize_of_nat(v___x_6715_);
                v___x_6725_ = 1usize;
                v___x_6726_ = lean_usize_sub(v___x_6724_, v___x_6725_);
                v___x_6727_ = lean_usize_land(v___x_6723_, v___x_6726_);
                v___x_6728_ = lean_array_uget_borrowed(v_x_6707_, v___x_6727_);
                leanh::lean_inc(v___x_6728_);
                if v_isShared_6714_ == 0 {
                    leanh::lean_ctor_set(v___x_6713_, 2, v___x_6728_);
                    v___x_6730_ = v___x_6713_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6733_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6733_, 0, v_key_6709_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6733_, 1, v_value_6710_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6733_, 2, v___x_6728_);
                    v___x_6730_ = v_reuseFailAlloc_6733_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6731_ = lean_array_uset(v_x_6707_, v___x_6727_, v___x_6730_);
                v_x_6707_ = v___x_6731_;
                v_x_6708_ = v_tail_6711_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(
    mut v_i_6735_: *mut leanh::LeanObject,
    mut v_source_6736_: *mut leanh::LeanObject,
    mut v_target_6737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6739_: u8 = 0;
    let mut v_es_6740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_6742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_6743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6738_ = lean_array_get_size(v_source_6736_);
                v___x_6739_ = lean_nat_dec_lt(v_i_6735_, v___x_6738_);
                if v___x_6739_ == 0 {
                    leanh::lean_dec_ref(v_source_6736_);
                    leanh::lean_dec(v_i_6735_);
                    return v_target_6737_;
                } else {
                    v_es_6740_ = lean_array_fget(v_source_6736_, v_i_6735_);
                    v___x_6741_ = leanh::lean_box(0);
                    v_source_6742_ = lean_array_fset(v_source_6736_, v_i_6735_, v___x_6741_);
                    v_target_6743_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_6737_, v_es_6740_);
                    v___x_6744_ = leanh::lean_unsigned_to_nat(1);
                    v___x_6745_ = lean_nat_add(v_i_6735_, v___x_6744_);
                    leanh::lean_dec(v_i_6735_);
                    v_i_6735_ = v___x_6745_;
                    v_source_6736_ = v_source_6742_;
                    v_target_6737_ = v_target_6743_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(
    mut v_data_6747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_6750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6748_ = lean_array_get_size(v_data_6747_);
    v___x_6749_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_6750_ = lean_nat_mul(v___x_6748_, v___x_6749_);
    v___x_6751_ = leanh::lean_unsigned_to_nat(0);
    v___x_6752_ = leanh::lean_box(0);
    v___x_6753_ = lean_mk_array(v_nbuckets_6750_, v___x_6752_);
    v___x_6754_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_6751_, v_data_6747_, v___x_6753_);
    return v___x_6754_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(
    mut v_a_6755_: *mut leanh::LeanObject,
    mut v_b_6756_: *mut leanh::LeanObject,
    mut v_x_6757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_6758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6763_: u8 = 0;
    let mut v___x_6764_: u8 = 0;
    let mut v___x_6765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6772_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6757_) == 0 {
                    leanh::lean_dec(v_b_6756_);
                    leanh::lean_dec_ref(v_a_6755_);
                    return v_x_6757_;
                } else {
                    v_key_6758_ = leanh::lean_ctor_get(v_x_6757_, 0);
                    v_value_6759_ = leanh::lean_ctor_get(v_x_6757_, 1);
                    v_tail_6760_ = leanh::lean_ctor_get(v_x_6757_, 2);
                    v_isSharedCheck_6772_ = (!leanh::lean_is_exclusive(v_x_6757_)) as u8;
                    if v_isSharedCheck_6772_ == 0 {
                        v___x_6762_ = v_x_6757_;
                        v_isShared_6763_ = v_isSharedCheck_6772_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_6760_);
                        leanh::lean_inc(v_value_6759_);
                        leanh::lean_inc(v_key_6758_);
                        leanh::lean_dec(v_x_6757_);
                        v___x_6762_ = leanh::lean_box(0);
                        v_isShared_6763_ = v_isSharedCheck_6772_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6764_ = l_Lean_ExprStructEq_beq(v_key_6758_, v_a_6755_);
                if v___x_6764_ == 0 {
                    v___x_6765_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_6755_, v_b_6756_, v_tail_6760_);
                    if v_isShared_6763_ == 0 {
                        leanh::lean_ctor_set(v___x_6762_, 2, v___x_6765_);
                        v___x_6767_ = v___x_6762_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6768_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6768_, 0, v_key_6758_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6768_, 1, v_value_6759_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6768_, 2, v___x_6765_);
                        v___x_6767_ = v_reuseFailAlloc_6768_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_6759_);
                    leanh::lean_dec(v_key_6758_);
                    if v_isShared_6763_ == 0 {
                        leanh::lean_ctor_set(v___x_6762_, 1, v_b_6756_);
                        leanh::lean_ctor_set(v___x_6762_, 0, v_a_6755_);
                        v___x_6770_ = v___x_6762_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6771_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6771_, 0, v_a_6755_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6771_, 1, v_b_6756_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6771_, 2, v_tail_6760_);
                        v___x_6770_ = v_reuseFailAlloc_6771_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6767_;
            }
            3 => {
                return v___x_6770_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(
    mut v_m_6773_: *mut leanh::LeanObject,
    mut v_a_6774_: *mut leanh::LeanObject,
    mut v_b_6775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_6776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_6777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6780_: u8 = 0;
    let mut v___x_6781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6782_: u64 = 0;
    let mut v___x_6783_: u64 = 0;
    let mut v___x_6784_: u64 = 0;
    let mut v_fold_6785_: u64 = 0;
    let mut v___x_6786_: u64 = 0;
    let mut v___x_6787_: u64 = 0;
    let mut v___x_6788_: u64 = 0;
    let mut v___x_6789_: usize = 0;
    let mut v___x_6790_: usize = 0;
    let mut v___x_6791_: usize = 0;
    let mut v___x_6792_: usize = 0;
    let mut v___x_6793_: usize = 0;
    let mut v_bkt_6794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6795_: u8 = 0;
    let mut v___x_6796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_6797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_6799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6805_: u8 = 0;
    let mut v_val_6806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_6814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6820_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_6776_ = leanh::lean_ctor_get(v_m_6773_, 0);
                v_buckets_6777_ = leanh::lean_ctor_get(v_m_6773_, 1);
                v_isSharedCheck_6820_ = (!leanh::lean_is_exclusive(v_m_6773_)) as u8;
                if v_isSharedCheck_6820_ == 0 {
                    v___x_6779_ = v_m_6773_;
                    v_isShared_6780_ = v_isSharedCheck_6820_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_6777_);
                    leanh::lean_inc(v_size_6776_);
                    leanh::lean_dec(v_m_6773_);
                    v___x_6779_ = leanh::lean_box(0);
                    v_isShared_6780_ = v_isSharedCheck_6820_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6781_ = lean_array_get_size(v_buckets_6777_);
                v___x_6782_ = l_Lean_ExprStructEq_hash(v_a_6774_);
                v___x_6783_ = 32u64;
                v___x_6784_ = lean_uint64_shift_right(v___x_6782_, v___x_6783_);
                v_fold_6785_ = lean_uint64_xor(v___x_6782_, v___x_6784_);
                v___x_6786_ = 16u64;
                v___x_6787_ = lean_uint64_shift_right(v_fold_6785_, v___x_6786_);
                v___x_6788_ = lean_uint64_xor(v_fold_6785_, v___x_6787_);
                v___x_6789_ = lean_uint64_to_usize(v___x_6788_);
                v___x_6790_ = lean_usize_of_nat(v___x_6781_);
                v___x_6791_ = 1usize;
                v___x_6792_ = lean_usize_sub(v___x_6790_, v___x_6791_);
                v___x_6793_ = lean_usize_land(v___x_6789_, v___x_6792_);
                v_bkt_6794_ = lean_array_uget_borrowed(v_buckets_6777_, v___x_6793_);
                v___x_6795_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_6774_, v_bkt_6794_);
                if v___x_6795_ == 0 {
                    v___x_6796_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_6797_ = lean_nat_add(v_size_6776_, v___x_6796_);
                    leanh::lean_dec(v_size_6776_);
                    leanh::lean_inc(v_bkt_6794_);
                    v___x_6798_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_6798_, 0, v_a_6774_);
                    leanh::lean_ctor_set(v___x_6798_, 1, v_b_6775_);
                    leanh::lean_ctor_set(v___x_6798_, 2, v_bkt_6794_);
                    v_buckets_x27_6799_ =
                        lean_array_uset(v_buckets_6777_, v___x_6793_, v___x_6798_);
                    v___x_6800_ = leanh::lean_unsigned_to_nat(4);
                    v___x_6801_ = lean_nat_mul(v_size_x27_6797_, v___x_6800_);
                    v___x_6802_ = leanh::lean_unsigned_to_nat(3);
                    v___x_6803_ = lean_nat_div(v___x_6801_, v___x_6802_);
                    leanh::lean_dec(v___x_6801_);
                    v___x_6804_ = lean_array_get_size(v_buckets_x27_6799_);
                    v___x_6805_ = lean_nat_dec_le(v___x_6803_, v___x_6804_);
                    leanh::lean_dec(v___x_6803_);
                    if v___x_6805_ == 0 {
                        v_val_6806_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_6799_);
                        if v_isShared_6780_ == 0 {
                            leanh::lean_ctor_set(v___x_6779_, 1, v_val_6806_);
                            leanh::lean_ctor_set(v___x_6779_, 0, v_size_x27_6797_);
                            v___x_6808_ = v___x_6779_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_6809_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_6809_,
                                0,
                                v_size_x27_6797_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_6809_, 1, v_val_6806_);
                            v___x_6808_ = v_reuseFailAlloc_6809_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_6780_ == 0 {
                            leanh::lean_ctor_set(v___x_6779_, 1, v_buckets_x27_6799_);
                            leanh::lean_ctor_set(v___x_6779_, 0, v_size_x27_6797_);
                            v___x_6811_ = v___x_6779_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6812_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_6812_,
                                0,
                                v_size_x27_6797_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_6812_,
                                1,
                                v_buckets_x27_6799_,
                            );
                            v___x_6811_ = v_reuseFailAlloc_6812_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_6794_);
                    v___x_6813_ = leanh::lean_box(0);
                    v_buckets_x27_6814_ =
                        lean_array_uset(v_buckets_6777_, v___x_6793_, v___x_6813_);
                    v___x_6815_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_6774_, v_b_6775_, v_bkt_6794_);
                    v___x_6816_ = lean_array_uset(v_buckets_x27_6814_, v___x_6793_, v___x_6815_);
                    if v_isShared_6780_ == 0 {
                        leanh::lean_ctor_set(v___x_6779_, 1, v___x_6816_);
                        v___x_6818_ = v___x_6779_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6819_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6819_, 0, v_size_6776_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6819_, 1, v___x_6816_);
                        v___x_6818_ = v_reuseFailAlloc_6819_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6808_;
            }
            3 => {
                return v___x_6811_;
            }
            4 => {
                return v___x_6818_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(
    mut v_a_6821_: *mut leanh::LeanObject,
    mut v_e_6822_: *mut leanh::LeanObject,
    mut v_a_6823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6825_ = lean_st_ref_take(v_a_6821_);
    v___x_6826_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v___x_6825_, v_e_6822_, v_a_6823_);
    v___x_6827_ = lean_st_ref_set(v_a_6821_, v___x_6826_);
    v___x_6828_ = leanh::lean_box(0);
    return v___x_6828_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed(
    mut v_a_6829_: *mut leanh::LeanObject,
    mut v_e_6830_: *mut leanh::LeanObject,
    mut v_a_6831_: *mut leanh::LeanObject,
    mut v___y_6832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6833_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(v_a_6829_, v_e_6830_, v_a_6831_);
    leanh::lean_dec(v_a_6829_);
    return v_res_6833_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(
    mut v_a_6834_: *mut leanh::LeanObject,
    mut v_x_6835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_6837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6840_: u8 = 0;
    let mut v___x_6842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6835_) == 0 {
                    v___x_6836_ = leanh::lean_box(0);
                    return v___x_6836_;
                } else {
                    v_key_6837_ = leanh::lean_ctor_get(v_x_6835_, 0);
                    v_value_6838_ = leanh::lean_ctor_get(v_x_6835_, 1);
                    v_tail_6839_ = leanh::lean_ctor_get(v_x_6835_, 2);
                    v___x_6840_ = l_Lean_ExprStructEq_beq(v_key_6837_, v_a_6834_);
                    if v___x_6840_ == 0 {
                        v_x_6835_ = v_tail_6839_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_6838_);
                        v___x_6842_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_6842_, 0, v_value_6838_);
                        return v___x_6842_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg___boxed(
    mut v_a_6843_: *mut leanh::LeanObject,
    mut v_x_6844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6845_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_6843_, v_x_6844_);
    leanh::lean_dec(v_x_6844_);
    leanh::lean_dec_ref(v_a_6843_);
    return v_res_6845_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(
    mut v_m_6846_: *mut leanh::LeanObject,
    mut v_a_6847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_6848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: u64 = 0;
    let mut v___x_6851_: u64 = 0;
    let mut v___x_6852_: u64 = 0;
    let mut v_fold_6853_: u64 = 0;
    let mut v___x_6854_: u64 = 0;
    let mut v___x_6855_: u64 = 0;
    let mut v___x_6856_: u64 = 0;
    let mut v___x_6857_: usize = 0;
    let mut v___x_6858_: usize = 0;
    let mut v___x_6859_: usize = 0;
    let mut v___x_6860_: usize = 0;
    let mut v___x_6861_: usize = 0;
    let mut v___x_6862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_6848_ = leanh::lean_ctor_get(v_m_6846_, 1);
    v___x_6849_ = lean_array_get_size(v_buckets_6848_);
    v___x_6850_ = l_Lean_ExprStructEq_hash(v_a_6847_);
    v___x_6851_ = 32u64;
    v___x_6852_ = lean_uint64_shift_right(v___x_6850_, v___x_6851_);
    v_fold_6853_ = lean_uint64_xor(v___x_6850_, v___x_6852_);
    v___x_6854_ = 16u64;
    v___x_6855_ = lean_uint64_shift_right(v_fold_6853_, v___x_6854_);
    v___x_6856_ = lean_uint64_xor(v_fold_6853_, v___x_6855_);
    v___x_6857_ = lean_uint64_to_usize(v___x_6856_);
    v___x_6858_ = lean_usize_of_nat(v___x_6849_);
    v___x_6859_ = 1usize;
    v___x_6860_ = lean_usize_sub(v___x_6858_, v___x_6859_);
    v___x_6861_ = lean_usize_land(v___x_6857_, v___x_6860_);
    v___x_6862_ = lean_array_uget_borrowed(v_buckets_6848_, v___x_6861_);
    v___x_6863_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_6847_, v___x_6862_);
    return v___x_6863_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_m_6864_: *mut leanh::LeanObject,
    mut v_a_6865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6866_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_m_6864_, v_a_6865_);
    leanh::lean_dec_ref(v_a_6865_);
    leanh::lean_dec_ref(v_m_6864_);
    return v_res_6866_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(
    mut v_pre_6867_: *mut leanh::LeanObject,
    mut v_post_6868_: *mut leanh::LeanObject,
    mut v_sz_6869_: usize,
    mut v_i_6870_: usize,
    mut v_bs_6871_: *mut leanh::LeanObject,
    mut v___y_6872_: *mut leanh::LeanObject,
    mut v___y_6873_: *mut leanh::LeanObject,
    mut v___y_6874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6876_: u8 = 0;
    let mut v___x_6877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6883_: usize = 0;
    let mut v___x_6884_: usize = 0;
    let mut v___x_6885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6890_: u8 = 0;
    let mut v___x_6892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6894_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6876_ = lean_usize_dec_lt(v_i_6870_, v_sz_6869_);
                if v___x_6876_ == 0 {
                    leanh::lean_dec_ref(v_post_6868_);
                    leanh::lean_dec_ref(v_pre_6867_);
                    v___x_6877_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6877_, 0, v_bs_6871_);
                    return v___x_6877_;
                } else {
                    v_v_6878_ = lean_array_uget_borrowed(v_bs_6871_, v_i_6870_);
                    leanh::lean_inc(v_v_6878_);
                    leanh::lean_inc_ref(v_post_6868_);
                    leanh::lean_inc_ref(v_pre_6867_);
                    v___x_6879_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_6867_, v_post_6868_, v_v_6878_, v___y_6872_, v___y_6873_, v___y_6874_);
                    if leanh::lean_obj_tag(v___x_6879_) == 0 {
                        v_a_6880_ = leanh::lean_ctor_get(v___x_6879_, 0);
                        leanh::lean_inc(v_a_6880_);
                        leanh::lean_dec_ref_known(v___x_6879_, 1);
                        v___x_6881_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_6882_ = lean_array_uset(v_bs_6871_, v_i_6870_, v___x_6881_);
                        v___x_6883_ = 1usize;
                        v___x_6884_ = lean_usize_add(v_i_6870_, v___x_6883_);
                        v___x_6885_ = lean_array_uset(v_bs_x27_6882_, v_i_6870_, v_a_6880_);
                        v_i_6870_ = v___x_6884_;
                        v_bs_6871_ = v___x_6885_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_6871_);
                        leanh::lean_dec_ref(v_post_6868_);
                        leanh::lean_dec_ref(v_pre_6867_);
                        v_a_6887_ = leanh::lean_ctor_get(v___x_6879_, 0);
                        v_isSharedCheck_6894_ =
                            (!leanh::lean_is_exclusive(v___x_6879_)) as u8;
                        if v_isSharedCheck_6894_ == 0 {
                            v___x_6889_ = v___x_6879_;
                            v_isShared_6890_ = v_isSharedCheck_6894_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6887_);
                            leanh::lean_dec(v___x_6879_);
                            v___x_6889_ = leanh::lean_box(0);
                            v_isShared_6890_ = v_isSharedCheck_6894_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6890_ == 0 {
                    v___x_6892_ = v___x_6889_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6893_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6893_, 0, v_a_6887_);
                    v___x_6892_ = v_reuseFailAlloc_6893_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6892_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(
    mut v_pre_6895_: *mut leanh::LeanObject,
    mut v_post_6896_: *mut leanh::LeanObject,
    mut v_x_6897_: *mut leanh::LeanObject,
    mut v_x_6898_: *mut leanh::LeanObject,
    mut v_x_6899_: *mut leanh::LeanObject,
    mut v___y_6900_: *mut leanh::LeanObject,
    mut v___y_6901_: *mut leanh::LeanObject,
    mut v___y_6902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fn_6904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_6905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6912_: usize = 0;
    let mut v___x_6913_: usize = 0;
    let mut v___x_6914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6921_: u8 = 0;
    let mut v___x_6923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6925_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6897_) == 5 {
                    v_fn_6904_ = leanh::lean_ctor_get(v_x_6897_, 0);
                    leanh::lean_inc_ref(v_fn_6904_);
                    v_arg_6905_ = leanh::lean_ctor_get(v_x_6897_, 1);
                    leanh::lean_inc_ref(v_arg_6905_);
                    leanh::lean_dec_ref_known(v_x_6897_, 2);
                    v___x_6906_ = lean_array_set(v_x_6898_, v_x_6899_, v_arg_6905_);
                    v___x_6907_ = leanh::lean_unsigned_to_nat(1);
                    v___x_6908_ = lean_nat_sub(v_x_6899_, v___x_6907_);
                    leanh::lean_dec(v_x_6899_);
                    v_x_6897_ = v_fn_6904_;
                    v_x_6898_ = v___x_6906_;
                    v_x_6899_ = v___x_6908_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_x_6899_);
                    leanh::lean_inc_ref(v_post_6896_);
                    leanh::lean_inc_ref(v_pre_6895_);
                    v___x_6910_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_6895_, v_post_6896_, v_x_6897_, v___y_6900_, v___y_6901_, v___y_6902_);
                    if leanh::lean_obj_tag(v___x_6910_) == 0 {
                        v_a_6911_ = leanh::lean_ctor_get(v___x_6910_, 0);
                        leanh::lean_inc(v_a_6911_);
                        leanh::lean_dec_ref_known(v___x_6910_, 1);
                        v_sz_6912_ = lean_array_size(v_x_6898_);
                        v___x_6913_ = 0usize;
                        leanh::lean_inc_ref(v_post_6896_);
                        leanh::lean_inc_ref(v_pre_6895_);
                        v___x_6914_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(v_pre_6895_, v_post_6896_, v_sz_6912_, v___x_6913_, v_x_6898_, v___y_6900_, v___y_6901_, v___y_6902_);
                        if leanh::lean_obj_tag(v___x_6914_) == 0 {
                            v_a_6915_ = leanh::lean_ctor_get(v___x_6914_, 0);
                            leanh::lean_inc(v_a_6915_);
                            leanh::lean_dec_ref_known(v___x_6914_, 1);
                            v___x_6916_ = l_Lean_mkAppN(v_a_6911_, v_a_6915_);
                            leanh::lean_dec(v_a_6915_);
                            v___x_6917_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_6895_, v_post_6896_, v___x_6916_, v___y_6900_, v___y_6901_, v___y_6902_);
                            return v___x_6917_;
                        } else {
                            leanh::lean_dec(v_a_6911_);
                            leanh::lean_dec_ref(v_post_6896_);
                            leanh::lean_dec_ref(v_pre_6895_);
                            v_a_6918_ = leanh::lean_ctor_get(v___x_6914_, 0);
                            v_isSharedCheck_6925_ =
                                (!leanh::lean_is_exclusive(v___x_6914_)) as u8;
                            if v_isSharedCheck_6925_ == 0 {
                                v___x_6920_ = v___x_6914_;
                                v_isShared_6921_ = v_isSharedCheck_6925_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6918_);
                                leanh::lean_dec(v___x_6914_);
                                v___x_6920_ = leanh::lean_box(0);
                                v_isShared_6921_ = v_isSharedCheck_6925_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_x_6898_);
                        leanh::lean_dec_ref(v_post_6896_);
                        leanh::lean_dec_ref(v_pre_6895_);
                        return v___x_6910_;
                    }
                }
            }
            1 => {
                if v_isShared_6921_ == 0 {
                    v___x_6923_ = v___x_6920_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6924_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6924_, 0, v_a_6918_);
                    v___x_6923_ = v_reuseFailAlloc_6924_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6923_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(
    mut v___x_6926_: *mut leanh::LeanObject,
    mut v_pre_6927_: *mut leanh::LeanObject,
    mut v_e_6928_: *mut leanh::LeanObject,
    mut v_post_6929_: *mut leanh::LeanObject,
    mut v___y_6930_: *mut leanh::LeanObject,
    mut v___y_6931_: *mut leanh::LeanObject,
    mut v___y_6932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6937_: u8 = 0;
    let mut v___y_6938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6942_: u8 = 0;
    let mut v___x_6943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6945_: usize = 0;
    let mut v___x_6946_: usize = 0;
    let mut v___x_6947_: u8 = 0;
    let mut v___x_6948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6953_: u8 = 0;
    let mut v___y_6954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6957_: u8 = 0;
    let mut v___x_6958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6960_: u8 = 0;
    let mut v___x_6961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6966_: u8 = 0;
    let mut v___y_6967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6970_: u8 = 0;
    let mut v___x_6971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6973_: u8 = 0;
    let mut v___x_6974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6982_: u8 = 0;
    let mut v___y_6984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_6985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_6986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_6988_: u8 = 0;
    let mut v___x_6989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6993_: usize = 0;
    let mut v___x_6994_: usize = 0;
    let mut v___x_6995_: u8 = 0;
    let mut v___x_6996_: usize = 0;
    let mut v___x_6997_: usize = 0;
    let mut v___x_6998_: u8 = 0;
    let mut v_binderName_6999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_7000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_7001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_7002_: u8 = 0;
    let mut v___x_7003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7007_: usize = 0;
    let mut v___x_7008_: usize = 0;
    let mut v___x_7009_: u8 = 0;
    let mut v___x_7010_: usize = 0;
    let mut v___x_7011_: usize = 0;
    let mut v___x_7012_: u8 = 0;
    let mut v_declName_7013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_7016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_7017_: u8 = 0;
    let mut v___x_7018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7024_: usize = 0;
    let mut v___x_7025_: usize = 0;
    let mut v___x_7026_: u8 = 0;
    let mut v___x_7027_: usize = 0;
    let mut v___x_7028_: usize = 0;
    let mut v___x_7029_: u8 = 0;
    let mut v_dummy_7030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_7031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_7036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_7037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7040_: usize = 0;
    let mut v___x_7041_: usize = 0;
    let mut v___x_7042_: u8 = 0;
    let mut v___x_7043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_7046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_7047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_7048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7051_: usize = 0;
    let mut v___x_7052_: usize = 0;
    let mut v___x_7053_: u8 = 0;
    let mut v___x_7054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_7058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_7062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_7066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7068_: u8 = 0;
    let mut v_a_7069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7072_: u8 = 0;
    let mut v___x_7074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7076_: u8 = 0;
    let mut v_a_7077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7080_: u8 = 0;
    let mut v___x_7082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7084_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6977_ = l_Lean_Core_checkSystem(v___x_6926_, v___y_6931_, v___y_6932_);
                if leanh::lean_obj_tag(v___x_6977_) == 0 {
                    leanh::lean_dec_ref_known(v___x_6977_, 1);
                    leanh::lean_inc_ref(v_pre_6927_);
                    leanh::lean_inc(v___y_6932_);
                    leanh::lean_inc_ref(v___y_6931_);
                    leanh::lean_inc_ref(v_e_6928_);
                    v___x_6978_ = leanh::lean_apply_4(
                        v_pre_6927_,
                        v_e_6928_,
                        v___y_6931_,
                        v___y_6932_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_6978_) == 0 {
                        v_a_6979_ = leanh::lean_ctor_get(v___x_6978_, 0);
                        v_isSharedCheck_7068_ =
                            (!leanh::lean_is_exclusive(v___x_6978_)) as u8;
                        if v_isSharedCheck_7068_ == 0 {
                            v___x_6981_ = v___x_6978_;
                            v_isShared_6982_ = v_isSharedCheck_7068_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6979_);
                            leanh::lean_dec(v___x_6978_);
                            v___x_6981_ = leanh::lean_box(0);
                            v_isShared_6982_ = v_isSharedCheck_7068_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_post_6929_);
                        leanh::lean_dec_ref(v_e_6928_);
                        leanh::lean_dec_ref(v_pre_6927_);
                        v_a_7069_ = leanh::lean_ctor_get(v___x_6978_, 0);
                        v_isSharedCheck_7076_ =
                            (!leanh::lean_is_exclusive(v___x_6978_)) as u8;
                        if v_isSharedCheck_7076_ == 0 {
                            v___x_7071_ = v___x_6978_;
                            v_isShared_7072_ = v_isSharedCheck_7076_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7069_);
                            leanh::lean_dec(v___x_6978_);
                            v___x_7071_ = leanh::lean_box(0);
                            v_isShared_7072_ = v_isSharedCheck_7076_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_post_6929_);
                    leanh::lean_dec_ref(v_e_6928_);
                    leanh::lean_dec_ref(v_pre_6927_);
                    v_a_7077_ = leanh::lean_ctor_get(v___x_6977_, 0);
                    v_isSharedCheck_7084_ = (!leanh::lean_is_exclusive(v___x_6977_)) as u8;
                    if v_isSharedCheck_7084_ == 0 {
                        v___x_7079_ = v___x_6977_;
                        v_isShared_7080_ = v_isSharedCheck_7084_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7077_);
                        leanh::lean_dec(v___x_6977_);
                        v___x_7079_ = leanh::lean_box(0);
                        v_isShared_7080_ = v_isSharedCheck_7084_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_6942_ == 0 {
                    leanh::lean_dec_ref(v___y_6936_);
                    leanh::lean_dec_ref(v___y_6935_);
                    v___x_6943_ = l_Lean_Expr_letE___override(
                        v___y_6938_,
                        v___y_6941_,
                        v___y_6940_,
                        v___y_6939_,
                        v___y_6937_,
                    );
                    v___x_6944_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_6927_, v_post_6929_, v___x_6943_, v___y_6930_, v___y_6931_, v___y_6932_);
                    return v___x_6944_;
                } else {
                    v___x_6945_ = lean_ptr_addr(v___y_6936_);
                    leanh::lean_dec_ref(v___y_6936_);
                    v___x_6946_ = lean_ptr_addr(v___y_6939_);
                    v___x_6947_ = lean_usize_dec_eq(v___x_6945_, v___x_6946_);
                    if v___x_6947_ == 0 {
                        leanh::lean_dec_ref(v___y_6935_);
                        v___x_6948_ = l_Lean_Expr_letE___override(
                            v___y_6938_,
                            v___y_6941_,
                            v___y_6940_,
                            v___y_6939_,
                            v___y_6937_,
                        );
                        v___x_6949_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_6927_, v_post_6929_, v___x_6948_, v___y_6930_, v___y_6931_, v___y_6932_);
                        return v___x_6949_;
                    } else {
                        leanh::lean_dec_ref(v___y_6941_);
                        leanh::lean_dec_ref(v___y_6940_);
                        leanh::lean_dec_ref(v___y_6939_);
                        leanh::lean_dec(v___y_6938_);
                        v___x_6950_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_6927_, v_post_6929_, v___y_6935_, v___y_6930_, v___y_6931_, v___y_6932_);
                        return v___x_6950_;
                    }
                }
            }
            2 => {
                if v___y_6957_ == 0 {
                    leanh::lean_dec_ref(v___y_6952_);
                    v___x_6958_ = l_Lean_Expr_lam___override(
                        v___y_6954_,
                        v___y_6955_,
                        v___y_6956_,
                        v___y_6953_,
                    );
                    v___x_6959_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_6927_, v_post_6929_, v___x_6958_, v___y_6930_, v___y_6931_, v___y_6932_);
                    return v___x_6959_;
                } else {
                    v___x_6960_ = l_Lean_instBEqBinderInfo_beq(v___y_6953_, v___y_6953_);
                    if v___x_6960_ == 0 {
                        leanh::lean_dec_ref(v___y_6952_);
                        v___x_6961_ = l_Lean_Expr_lam___override(
                            v___y_6954_,
                            v___y_6955_,
                            v___y_6956_,
                            v___y_6953_,
                        );
                        v___x_6962_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_6927_, v_post_6929_, v___x_6961_, v___y_6930_, v___y_6931_, v___y_6932_);
                        return v___x_6962_;
                    } else {
                        leanh::lean_dec_ref(v___y_6956_);
                        leanh::lean_dec_ref(v___y_6955_);
                        leanh::lean_dec(v___y_6954_);
                        v___x_6963_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_6927_, v_post_6929_, v___y_6952_, v___y_6930_, v___y_6931_, v___y_6932_);
                        return v___x_6963_;
                    }
                }
            }
            3 => {
                if v___y_6970_ == 0 {
                    leanh::lean_dec_ref(v___y_6965_);
                    v___x_6971_ = l_Lean_Expr_forallE___override(
                        v___y_6968_,
                        v___y_6967_,
                        v___y_6969_,
                        v___y_6966_,
                    );
                    v___x_6972_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_6927_, v_post_6929_, v___x_6971_, v___y_6930_, v___y_6931_, v___y_6932_);
                    return v___x_6972_;
                } else {
                    v___x_6973_ = l_Lean_instBEqBinderInfo_beq(v___y_6966_, v___y_6966_);
                    if v___x_6973_ == 0 {
                        leanh::lean_dec_ref(v___y_6965_);
                        v___x_6974_ = l_Lean_Expr_forallE___override(
                            v___y_6968_,
                            v___y_6967_,
                            v___y_6969_,
                            v___y_6966_,
                        );
                        v___x_6975_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_6927_, v_post_6929_, v___x_6974_, v___y_6930_, v___y_6931_, v___y_6932_);
                        return v___x_6975_;
                    } else {
                        leanh::lean_dec_ref(v___y_6969_);
                        leanh::lean_dec(v___y_6968_);
                        leanh::lean_dec_ref(v___y_6967_);
                        v___x_6976_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_6927_, v_post_6929_, v___y_6965_, v___y_6930_, v___y_6931_, v___y_6932_);
                        return v___x_6976_;
                    }
                }
            }
            4 => match leanh::lean_obj_tag(v_a_6979_) {
                0 => {
                    leanh::lean_dec_ref(v_post_6929_);
                    leanh::lean_dec_ref(v_e_6928_);
                    leanh::lean_dec_ref(v_pre_6927_);
                    v_e_7058_ = leanh::lean_ctor_get(v_a_6979_, 0);
                    leanh::lean_inc_ref(v_e_7058_);
                    leanh::lean_dec_ref_known(v_a_6979_, 1);
                    if v_isShared_6982_ == 0 {
                        leanh::lean_ctor_set(v___x_6981_, 0, v_e_7058_);
                        v___x_7060_ = v___x_6981_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_7061_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7061_, 0, v_e_7058_);
                        v___x_7060_ = v_reuseFailAlloc_7061_;
                        state = 6;
                        continue;
                    }
                }
                1 => {
                    leanh::lean_del_object(v___x_6981_);
                    leanh::lean_dec_ref(v_e_6928_);
                    v_e_7062_ = leanh::lean_ctor_get(v_a_6979_, 0);
                    leanh::lean_inc_ref(v_e_7062_);
                    leanh::lean_dec_ref_known(v_a_6979_, 1);
                    leanh::lean_inc_ref(v_post_6929_);
                    leanh::lean_inc_ref(v_pre_6927_);
                    v___x_7063_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_6927_, v_post_6929_, v_e_7062_, v___y_6930_, v___y_6931_, v___y_6932_);
                    if leanh::lean_obj_tag(v___x_7063_) == 0 {
                        v_a_7064_ = leanh::lean_ctor_get(v___x_7063_, 0);
                        leanh::lean_inc(v_a_7064_);
                        leanh::lean_dec_ref_known(v___x_7063_, 1);
                        v___x_7065_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_6927_, v_post_6929_, v_a_7064_, v___y_6930_, v___y_6931_, v___y_6932_);
                        return v___x_7065_;
                    } else {
                        leanh::lean_dec_ref(v_post_6929_);
                        leanh::lean_dec_ref(v_pre_6927_);
                        return v___x_7063_;
                    }
                }
                _ => {
                    leanh::lean_del_object(v___x_6981_);
                    v_e_x3f_7066_ = leanh::lean_ctor_get(v_a_6979_, 0);
                    leanh::lean_inc(v_e_x3f_7066_);
                    leanh::lean_dec_ref_known(v_a_6979_, 1);
                    if leanh::lean_obj_tag(v_e_x3f_7066_) == 0 {
                        v___y_6984_ = v_e_6928_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_e_6928_);
                        v_val_7067_ = leanh::lean_ctor_get(v_e_x3f_7066_, 0);
                        leanh::lean_inc(v_val_7067_);
                        leanh::lean_dec_ref_known(v_e_x3f_7066_, 1);
                        v___y_6984_ = v_val_7067_;
                        state = 5;
                        continue;
                    }
                }
            },
            5 => match leanh::lean_obj_tag(v___y_6984_) {
                7 => {
                    v_binderName_6985_ = leanh::lean_ctor_get(v___y_6984_, 0);
                    leanh::lean_inc(v_binderName_6985_);
                    v_binderType_6986_ = leanh::lean_ctor_get(v___y_6984_, 1);
                    v_body_6987_ = leanh::lean_ctor_get(v___y_6984_, 2);
                    v_binderInfo_6988_ = leanh::lean_ctor_get_uint8(
                        v___y_6984_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    leanh::lean_inc_ref(v_binderType_6986_);
                    leanh::lean_inc_ref(v_post_6929_);
                    leanh::lean_inc_ref(v_pre_6927_);
                    v___x_6989_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_6927_, v_post_6929_, v_binderType_6986_, v___y_6930_, v___y_6931_, v___y_6932_);
                    if leanh::lean_obj_tag(v___x_6989_) == 0 {
                        v_a_6990_ = leanh::lean_ctor_get(v___x_6989_, 0);
                        leanh::lean_inc(v_a_6990_);
                        leanh::lean_dec_ref_known(v___x_6989_, 1);
                        leanh::lean_inc_ref(v_body_6987_);
                        leanh::lean_inc_ref(v_post_6929_);
                        leanh::lean_inc_ref(v_pre_6927_);
                        v___x_6991_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_6927_, v_post_6929_, v_body_6987_, v___y_6930_, v___y_6931_, v___y_6932_);
                        if leanh::lean_obj_tag(v___x_6991_) == 0 {
                            v_a_6992_ = leanh::lean_ctor_get(v___x_6991_, 0);
                            leanh::lean_inc(v_a_6992_);
                            leanh::lean_dec_ref_known(v___x_6991_, 1);
                            v___x_6993_ = lean_ptr_addr(v_binderType_6986_);
                            v___x_6994_ = lean_ptr_addr(v_a_6990_);
                            v___x_6995_ = lean_usize_dec_eq(v___x_6993_, v___x_6994_);
                            if v___x_6995_ == 0 {
                                v___y_6965_ = v___y_6984_;
                                v___y_6966_ = v_binderInfo_6988_;
                                v___y_6967_ = v_a_6990_;
                                v___y_6968_ = v_binderName_6985_;
                                v___y_6969_ = v_a_6992_;
                                v___y_6970_ = v___x_6995_;
                                state = 3;
                                continue;
                            } else {
                                v___x_6996_ = lean_ptr_addr(v_body_6987_);
                                v___x_6997_ = lean_ptr_addr(v_a_6992_);
                                v___x_6998_ = lean_usize_dec_eq(v___x_6996_, v___x_6997_);
                                v___y_6965_ = v___y_6984_;
                                v___y_6966_ = v_binderInfo_6988_;
                                v___y_6967_ = v_a_6990_;
                                v___y_6968_ = v_binderName_6985_;
                                v___y_6969_ = v_a_6992_;
                                v___y_6970_ = v___x_6998_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_6990_);
                            leanh::lean_dec(v_binderName_6985_);
                            leanh::lean_dec_ref_known(v___y_6984_, 3);
                            leanh::lean_dec_ref(v_post_6929_);
                            leanh::lean_dec_ref(v_pre_6927_);
                            return v___x_6991_;
                        }
                    } else {
                        leanh::lean_dec(v_binderName_6985_);
                        leanh::lean_dec_ref_known(v___y_6984_, 3);
                        leanh::lean_dec_ref(v_post_6929_);
                        leanh::lean_dec_ref(v_pre_6927_);
                        return v___x_6989_;
                    }
                }
                6 => {
                    v_binderName_6999_ = leanh::lean_ctor_get(v___y_6984_, 0);
                    leanh::lean_inc(v_binderName_6999_);
                    v_binderType_7000_ = leanh::lean_ctor_get(v___y_6984_, 1);
                    v_body_7001_ = leanh::lean_ctor_get(v___y_6984_, 2);
                    v_binderInfo_7002_ = leanh::lean_ctor_get_uint8(
                        v___y_6984_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    leanh::lean_inc_ref(v_binderType_7000_);
                    leanh::lean_inc_ref(v_post_6929_);
                    leanh::lean_inc_ref(v_pre_6927_);
                    v___x_7003_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_6927_, v_post_6929_, v_binderType_7000_, v___y_6930_, v___y_6931_, v___y_6932_);
                    if leanh::lean_obj_tag(v___x_7003_) == 0 {
                        v_a_7004_ = leanh::lean_ctor_get(v___x_7003_, 0);
                        leanh::lean_inc(v_a_7004_);
                        leanh::lean_dec_ref_known(v___x_7003_, 1);
                        leanh::lean_inc_ref(v_body_7001_);
                        leanh::lean_inc_ref(v_post_6929_);
                        leanh::lean_inc_ref(v_pre_6927_);
                        v___x_7005_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_6927_, v_post_6929_, v_body_7001_, v___y_6930_, v___y_6931_, v___y_6932_);
                        if leanh::lean_obj_tag(v___x_7005_) == 0 {
                            v_a_7006_ = leanh::lean_ctor_get(v___x_7005_, 0);
                            leanh::lean_inc(v_a_7006_);
                            leanh::lean_dec_ref_known(v___x_7005_, 1);
                            v___x_7007_ = lean_ptr_addr(v_binderType_7000_);
                            v___x_7008_ = lean_ptr_addr(v_a_7004_);
                            v___x_7009_ = lean_usize_dec_eq(v___x_7007_, v___x_7008_);
                            if v___x_7009_ == 0 {
                                v___y_6952_ = v___y_6984_;
                                v___y_6953_ = v_binderInfo_7002_;
                                v___y_6954_ = v_binderName_6999_;
                                v___y_6955_ = v_a_7004_;
                                v___y_6956_ = v_a_7006_;
                                v___y_6957_ = v___x_7009_;
                                state = 2;
                                continue;
                            } else {
                                v___x_7010_ = lean_ptr_addr(v_body_7001_);
                                v___x_7011_ = lean_ptr_addr(v_a_7006_);
                                v___x_7012_ = lean_usize_dec_eq(v___x_7010_, v___x_7011_);
                                v___y_6952_ = v___y_6984_;
                                v___y_6953_ = v_binderInfo_7002_;
                                v___y_6954_ = v_binderName_6999_;
                                v___y_6955_ = v_a_7004_;
                                v___y_6956_ = v_a_7006_;
                                v___y_6957_ = v___x_7012_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_7004_);
                            leanh::lean_dec_ref_known(v___y_6984_, 3);
                            leanh::lean_dec(v_binderName_6999_);
                            leanh::lean_dec_ref(v_post_6929_);
                            leanh::lean_dec_ref(v_pre_6927_);
                            return v___x_7005_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___y_6984_, 3);
                        leanh::lean_dec(v_binderName_6999_);
                        leanh::lean_dec_ref(v_post_6929_);
                        leanh::lean_dec_ref(v_pre_6927_);
                        return v___x_7003_;
                    }
                }
                8 => {
                    v_declName_7013_ = leanh::lean_ctor_get(v___y_6984_, 0);
                    leanh::lean_inc(v_declName_7013_);
                    v_type_7014_ = leanh::lean_ctor_get(v___y_6984_, 1);
                    v_value_7015_ = leanh::lean_ctor_get(v___y_6984_, 2);
                    v_body_7016_ = leanh::lean_ctor_get(v___y_6984_, 3);
                    leanh::lean_inc_ref(v_body_7016_);
                    v_nondep_7017_ = leanh::lean_ctor_get_uint8(
                        v___y_6984_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    leanh::lean_inc_ref(v_type_7014_);
                    leanh::lean_inc_ref(v_post_6929_);
                    leanh::lean_inc_ref(v_pre_6927_);
                    v___x_7018_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_6927_, v_post_6929_, v_type_7014_, v___y_6930_, v___y_6931_, v___y_6932_);
                    if leanh::lean_obj_tag(v___x_7018_) == 0 {
                        v_a_7019_ = leanh::lean_ctor_get(v___x_7018_, 0);
                        leanh::lean_inc(v_a_7019_);
                        leanh::lean_dec_ref_known(v___x_7018_, 1);
                        leanh::lean_inc_ref(v_value_7015_);
                        leanh::lean_inc_ref(v_post_6929_);
                        leanh::lean_inc_ref(v_pre_6927_);
                        v___x_7020_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_6927_, v_post_6929_, v_value_7015_, v___y_6930_, v___y_6931_, v___y_6932_);
                        if leanh::lean_obj_tag(v___x_7020_) == 0 {
                            v_a_7021_ = leanh::lean_ctor_get(v___x_7020_, 0);
                            leanh::lean_inc(v_a_7021_);
                            leanh::lean_dec_ref_known(v___x_7020_, 1);
                            leanh::lean_inc_ref(v_body_7016_);
                            leanh::lean_inc_ref(v_post_6929_);
                            leanh::lean_inc_ref(v_pre_6927_);
                            v___x_7022_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_6927_, v_post_6929_, v_body_7016_, v___y_6930_, v___y_6931_, v___y_6932_);
                            if leanh::lean_obj_tag(v___x_7022_) == 0 {
                                v_a_7023_ = leanh::lean_ctor_get(v___x_7022_, 0);
                                leanh::lean_inc(v_a_7023_);
                                leanh::lean_dec_ref_known(v___x_7022_, 1);
                                v___x_7024_ = lean_ptr_addr(v_type_7014_);
                                v___x_7025_ = lean_ptr_addr(v_a_7019_);
                                v___x_7026_ = lean_usize_dec_eq(v___x_7024_, v___x_7025_);
                                if v___x_7026_ == 0 {
                                    v___y_6935_ = v___y_6984_;
                                    v___y_6936_ = v_body_7016_;
                                    v___y_6937_ = v_nondep_7017_;
                                    v___y_6938_ = v_declName_7013_;
                                    v___y_6939_ = v_a_7023_;
                                    v___y_6940_ = v_a_7021_;
                                    v___y_6941_ = v_a_7019_;
                                    v___y_6942_ = v___x_7026_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_7027_ = lean_ptr_addr(v_value_7015_);
                                    v___x_7028_ = lean_ptr_addr(v_a_7021_);
                                    v___x_7029_ = lean_usize_dec_eq(v___x_7027_, v___x_7028_);
                                    v___y_6935_ = v___y_6984_;
                                    v___y_6936_ = v_body_7016_;
                                    v___y_6937_ = v_nondep_7017_;
                                    v___y_6938_ = v_declName_7013_;
                                    v___y_6939_ = v_a_7023_;
                                    v___y_6940_ = v_a_7021_;
                                    v___y_6941_ = v_a_7019_;
                                    v___y_6942_ = v___x_7029_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_7021_);
                                leanh::lean_dec(v_a_7019_);
                                leanh::lean_dec_ref(v_body_7016_);
                                leanh::lean_dec(v_declName_7013_);
                                leanh::lean_dec_ref_known(v___y_6984_, 4);
                                leanh::lean_dec_ref(v_post_6929_);
                                leanh::lean_dec_ref(v_pre_6927_);
                                return v___x_7022_;
                            }
                        } else {
                            leanh::lean_dec(v_a_7019_);
                            leanh::lean_dec_ref(v_body_7016_);
                            leanh::lean_dec(v_declName_7013_);
                            leanh::lean_dec_ref_known(v___y_6984_, 4);
                            leanh::lean_dec_ref(v_post_6929_);
                            leanh::lean_dec_ref(v_pre_6927_);
                            return v___x_7020_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_body_7016_);
                        leanh::lean_dec(v_declName_7013_);
                        leanh::lean_dec_ref_known(v___y_6984_, 4);
                        leanh::lean_dec_ref(v_post_6929_);
                        leanh::lean_dec_ref(v_pre_6927_);
                        return v___x_7018_;
                    }
                }
                5 => {
                    v_dummy_7030_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once), _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
                    v_nargs_7031_ = l_Lean_Expr_getAppNumArgs(v___y_6984_);
                    leanh::lean_inc(v_nargs_7031_);
                    v___x_7032_ = lean_mk_array(v_nargs_7031_, v_dummy_7030_);
                    v___x_7033_ = leanh::lean_unsigned_to_nat(1);
                    v___x_7034_ = lean_nat_sub(v_nargs_7031_, v___x_7033_);
                    leanh::lean_dec(v_nargs_7031_);
                    v___x_7035_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_6927_, v_post_6929_, v___y_6984_, v___x_7032_, v___x_7034_, v___y_6930_, v___y_6931_, v___y_6932_);
                    return v___x_7035_;
                }
                10 => {
                    v_data_7036_ = leanh::lean_ctor_get(v___y_6984_, 0);
                    v_expr_7037_ = leanh::lean_ctor_get(v___y_6984_, 1);
                    leanh::lean_inc_ref(v_expr_7037_);
                    leanh::lean_inc_ref(v_post_6929_);
                    leanh::lean_inc_ref(v_pre_6927_);
                    v___x_7038_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_6927_, v_post_6929_, v_expr_7037_, v___y_6930_, v___y_6931_, v___y_6932_);
                    if leanh::lean_obj_tag(v___x_7038_) == 0 {
                        v_a_7039_ = leanh::lean_ctor_get(v___x_7038_, 0);
                        leanh::lean_inc(v_a_7039_);
                        leanh::lean_dec_ref_known(v___x_7038_, 1);
                        v___x_7040_ = lean_ptr_addr(v_expr_7037_);
                        v___x_7041_ = lean_ptr_addr(v_a_7039_);
                        v___x_7042_ = lean_usize_dec_eq(v___x_7040_, v___x_7041_);
                        if v___x_7042_ == 0 {
                            leanh::lean_inc(v_data_7036_);
                            leanh::lean_dec_ref_known(v___y_6984_, 2);
                            v___x_7043_ = l_Lean_Expr_mdata___override(v_data_7036_, v_a_7039_);
                            v___x_7044_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_6927_, v_post_6929_, v___x_7043_, v___y_6930_, v___y_6931_, v___y_6932_);
                            return v___x_7044_;
                        } else {
                            leanh::lean_dec(v_a_7039_);
                            v___x_7045_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_6927_, v_post_6929_, v___y_6984_, v___y_6930_, v___y_6931_, v___y_6932_);
                            return v___x_7045_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___y_6984_, 2);
                        leanh::lean_dec_ref(v_post_6929_);
                        leanh::lean_dec_ref(v_pre_6927_);
                        return v___x_7038_;
                    }
                }
                11 => {
                    v_typeName_7046_ = leanh::lean_ctor_get(v___y_6984_, 0);
                    v_idx_7047_ = leanh::lean_ctor_get(v___y_6984_, 1);
                    v_struct_7048_ = leanh::lean_ctor_get(v___y_6984_, 2);
                    leanh::lean_inc_ref(v_struct_7048_);
                    leanh::lean_inc_ref(v_post_6929_);
                    leanh::lean_inc_ref(v_pre_6927_);
                    v___x_7049_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_6927_, v_post_6929_, v_struct_7048_, v___y_6930_, v___y_6931_, v___y_6932_);
                    if leanh::lean_obj_tag(v___x_7049_) == 0 {
                        v_a_7050_ = leanh::lean_ctor_get(v___x_7049_, 0);
                        leanh::lean_inc(v_a_7050_);
                        leanh::lean_dec_ref_known(v___x_7049_, 1);
                        v___x_7051_ = lean_ptr_addr(v_struct_7048_);
                        v___x_7052_ = lean_ptr_addr(v_a_7050_);
                        v___x_7053_ = lean_usize_dec_eq(v___x_7051_, v___x_7052_);
                        if v___x_7053_ == 0 {
                            leanh::lean_inc(v_idx_7047_);
                            leanh::lean_inc(v_typeName_7046_);
                            leanh::lean_dec_ref_known(v___y_6984_, 3);
                            v___x_7054_ = l_Lean_Expr_proj___override(
                                v_typeName_7046_,
                                v_idx_7047_,
                                v_a_7050_,
                            );
                            v___x_7055_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_6927_, v_post_6929_, v___x_7054_, v___y_6930_, v___y_6931_, v___y_6932_);
                            return v___x_7055_;
                        } else {
                            leanh::lean_dec(v_a_7050_);
                            v___x_7056_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_6927_, v_post_6929_, v___y_6984_, v___y_6930_, v___y_6931_, v___y_6932_);
                            return v___x_7056_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___y_6984_, 3);
                        leanh::lean_dec_ref(v_post_6929_);
                        leanh::lean_dec_ref(v_pre_6927_);
                        return v___x_7049_;
                    }
                }
                _ => {
                    v___x_7057_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_6927_, v_post_6929_, v___y_6984_, v___y_6930_, v___y_6931_, v___y_6932_);
                    return v___x_7057_;
                }
            },
            6 => {
                return v___x_7060_;
            }
            7 => {
                if v_isShared_7072_ == 0 {
                    v___x_7074_ = v___x_7071_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7075_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7075_, 0, v_a_7069_);
                    v___x_7074_ = v_reuseFailAlloc_7075_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7074_;
            }
            9 => {
                if v_isShared_7080_ == 0 {
                    v___x_7082_ = v___x_7079_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7083_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7083_, 0, v_a_7077_);
                    v___x_7082_ = v_reuseFailAlloc_7083_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7082_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed(
    mut v___x_7085_: *mut leanh::LeanObject,
    mut v_pre_7086_: *mut leanh::LeanObject,
    mut v_e_7087_: *mut leanh::LeanObject,
    mut v_post_7088_: *mut leanh::LeanObject,
    mut v___y_7089_: *mut leanh::LeanObject,
    mut v___y_7090_: *mut leanh::LeanObject,
    mut v___y_7091_: *mut leanh::LeanObject,
    mut v___y_7092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7093_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(v___x_7085_, v_pre_7086_, v_e_7087_, v_post_7088_, v___y_7089_, v___y_7090_, v___y_7091_);
    leanh::lean_dec(v___y_7091_);
    leanh::lean_dec_ref(v___y_7090_);
    leanh::lean_dec(v___y_7089_);
    return v_res_7093_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(
    mut v_pre_7094_: *mut leanh::LeanObject,
    mut v_post_7095_: *mut leanh::LeanObject,
    mut v_e_7096_: *mut leanh::LeanObject,
    mut v_a_7097_: *mut leanh::LeanObject,
    mut v___y_7098_: *mut leanh::LeanObject,
    mut v___y_7099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7106_: u8 = 0;
    let mut v___x_7107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7116_: u8 = 0;
    let mut v___x_7118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7120_: u8 = 0;
    let mut v_unused_7121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7125_: u8 = 0;
    let mut v___x_7127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7129_: u8 = 0;
    let mut v_val_7130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7134_: u8 = 0;
    let mut v_a_7135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7138_: u8 = 0;
    let mut v___x_7140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7142_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_7097_);
                v___x_7101_ = leanh::lean_alloc_closure(
                    l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___x_7101_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_7101_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_7101_, 2, v_a_7097_);
                v___x_7102_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(leanh::lean_box(0), v___x_7101_, v___y_7098_, v___y_7099_);
                if leanh::lean_obj_tag(v___x_7102_) == 0 {
                    v_a_7103_ = leanh::lean_ctor_get(v___x_7102_, 0);
                    v_isSharedCheck_7134_ = (!leanh::lean_is_exclusive(v___x_7102_)) as u8;
                    if v_isSharedCheck_7134_ == 0 {
                        v___x_7105_ = v___x_7102_;
                        v_isShared_7106_ = v_isSharedCheck_7134_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7103_);
                        leanh::lean_dec(v___x_7102_);
                        v___x_7105_ = leanh::lean_box(0);
                        v_isShared_7106_ = v_isSharedCheck_7134_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_7096_);
                    leanh::lean_dec_ref(v_post_7095_);
                    leanh::lean_dec_ref(v_pre_7094_);
                    v_a_7135_ = leanh::lean_ctor_get(v___x_7102_, 0);
                    v_isSharedCheck_7142_ = (!leanh::lean_is_exclusive(v___x_7102_)) as u8;
                    if v_isSharedCheck_7142_ == 0 {
                        v___x_7137_ = v___x_7102_;
                        v_isShared_7138_ = v_isSharedCheck_7142_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7135_);
                        leanh::lean_dec(v___x_7102_);
                        v___x_7137_ = leanh::lean_box(0);
                        v_isShared_7138_ = v_isSharedCheck_7142_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7107_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_a_7103_, v_e_7096_);
                leanh::lean_dec(v_a_7103_);
                if leanh::lean_obj_tag(v___x_7107_) == 0 {
                    leanh::lean_del_object(v___x_7105_);
                    v___x_7108_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0;
                    leanh::lean_inc_ref(v_e_7096_);
                    v___f_7109_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed as *mut core::ffi::c_void, 8, 4);
                    leanh::lean_closure_set(v___f_7109_, 0, v___x_7108_);
                    leanh::lean_closure_set(v___f_7109_, 1, v_pre_7094_);
                    leanh::lean_closure_set(v___f_7109_, 2, v_e_7096_);
                    leanh::lean_closure_set(v___f_7109_, 3, v_post_7095_);
                    v___x_7110_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v___f_7109_, v_a_7097_, v___y_7098_, v___y_7099_);
                    if leanh::lean_obj_tag(v___x_7110_) == 0 {
                        v_a_7111_ = leanh::lean_ctor_get(v___x_7110_, 0);
                        leanh::lean_inc_n(v_a_7111_, 2);
                        leanh::lean_dec_ref_known(v___x_7110_, 1);
                        leanh::lean_inc(v_a_7097_);
                        v___f_7112_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed as *mut core::ffi::c_void, 4, 3);
                        leanh::lean_closure_set(v___f_7112_, 0, v_a_7097_);
                        leanh::lean_closure_set(v___f_7112_, 1, v_e_7096_);
                        leanh::lean_closure_set(v___f_7112_, 2, v_a_7111_);
                        v___x_7113_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(leanh::lean_box(0), v___f_7112_, v___y_7098_, v___y_7099_);
                        if leanh::lean_obj_tag(v___x_7113_) == 0 {
                            v_isSharedCheck_7120_ =
                                (!leanh::lean_is_exclusive(v___x_7113_)) as u8;
                            if v_isSharedCheck_7120_ == 0 {
                                v_unused_7121_ = leanh::lean_ctor_get(v___x_7113_, 0);
                                leanh::lean_dec(v_unused_7121_);
                                v___x_7115_ = v___x_7113_;
                                v_isShared_7116_ = v_isSharedCheck_7120_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_7113_);
                                v___x_7115_ = leanh::lean_box(0);
                                v_isShared_7116_ = v_isSharedCheck_7120_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_7111_);
                            v_a_7122_ = leanh::lean_ctor_get(v___x_7113_, 0);
                            v_isSharedCheck_7129_ =
                                (!leanh::lean_is_exclusive(v___x_7113_)) as u8;
                            if v_isSharedCheck_7129_ == 0 {
                                v___x_7124_ = v___x_7113_;
                                v_isShared_7125_ = v_isSharedCheck_7129_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7122_);
                                leanh::lean_dec(v___x_7113_);
                                v___x_7124_ = leanh::lean_box(0);
                                v_isShared_7125_ = v_isSharedCheck_7129_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_7096_);
                        return v___x_7110_;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_7096_);
                    leanh::lean_dec_ref(v_post_7095_);
                    leanh::lean_dec_ref(v_pre_7094_);
                    v_val_7130_ = leanh::lean_ctor_get(v___x_7107_, 0);
                    leanh::lean_inc(v_val_7130_);
                    leanh::lean_dec_ref_known(v___x_7107_, 1);
                    if v_isShared_7106_ == 0 {
                        leanh::lean_ctor_set(v___x_7105_, 0, v_val_7130_);
                        v___x_7132_ = v___x_7105_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_7133_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7133_, 0, v_val_7130_);
                        v___x_7132_ = v_reuseFailAlloc_7133_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7116_ == 0 {
                    leanh::lean_ctor_set(v___x_7115_, 0, v_a_7111_);
                    v___x_7118_ = v___x_7115_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7119_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7119_, 0, v_a_7111_);
                    v___x_7118_ = v_reuseFailAlloc_7119_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7118_;
            }
            4 => {
                if v_isShared_7125_ == 0 {
                    v___x_7127_ = v___x_7124_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7128_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7128_, 0, v_a_7122_);
                    v___x_7127_ = v_reuseFailAlloc_7128_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7127_;
            }
            6 => {
                return v___x_7132_;
            }
            7 => {
                if v_isShared_7138_ == 0 {
                    v___x_7140_ = v___x_7137_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7141_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7141_, 0, v_a_7135_);
                    v___x_7140_ = v_reuseFailAlloc_7141_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7140_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(
    mut v_pre_7143_: *mut leanh::LeanObject,
    mut v_post_7144_: *mut leanh::LeanObject,
    mut v_e_7145_: *mut leanh::LeanObject,
    mut v_a_7146_: *mut leanh::LeanObject,
    mut v___y_7147_: *mut leanh::LeanObject,
    mut v___y_7148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7154_: u8 = 0;
    let mut v_e_7155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_7159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_7161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7169_: u8 = 0;
    let mut v_a_7170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7173_: u8 = 0;
    let mut v___x_7175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7177_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_post_7144_);
                leanh::lean_inc(v___y_7148_);
                leanh::lean_inc_ref(v___y_7147_);
                leanh::lean_inc_ref(v_e_7145_);
                v___x_7150_ = leanh::lean_apply_4(
                    v_post_7144_,
                    v_e_7145_,
                    v___y_7147_,
                    v___y_7148_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_7150_) == 0 {
                    v_a_7151_ = leanh::lean_ctor_get(v___x_7150_, 0);
                    v_isSharedCheck_7169_ = (!leanh::lean_is_exclusive(v___x_7150_)) as u8;
                    if v_isSharedCheck_7169_ == 0 {
                        v___x_7153_ = v___x_7150_;
                        v_isShared_7154_ = v_isSharedCheck_7169_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7151_);
                        leanh::lean_dec(v___x_7150_);
                        v___x_7153_ = leanh::lean_box(0);
                        v_isShared_7154_ = v_isSharedCheck_7169_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_7145_);
                    leanh::lean_dec_ref(v_post_7144_);
                    leanh::lean_dec_ref(v_pre_7143_);
                    v_a_7170_ = leanh::lean_ctor_get(v___x_7150_, 0);
                    v_isSharedCheck_7177_ = (!leanh::lean_is_exclusive(v___x_7150_)) as u8;
                    if v_isSharedCheck_7177_ == 0 {
                        v___x_7172_ = v___x_7150_;
                        v_isShared_7173_ = v_isSharedCheck_7177_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7170_);
                        leanh::lean_dec(v___x_7150_);
                        v___x_7172_ = leanh::lean_box(0);
                        v_isShared_7173_ = v_isSharedCheck_7177_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => match leanh::lean_obj_tag(v_a_7151_) {
                0 => {
                    leanh::lean_dec_ref(v_e_7145_);
                    leanh::lean_dec_ref(v_post_7144_);
                    leanh::lean_dec_ref(v_pre_7143_);
                    v_e_7155_ = leanh::lean_ctor_get(v_a_7151_, 0);
                    leanh::lean_inc_ref(v_e_7155_);
                    leanh::lean_dec_ref_known(v_a_7151_, 1);
                    if v_isShared_7154_ == 0 {
                        leanh::lean_ctor_set(v___x_7153_, 0, v_e_7155_);
                        v___x_7157_ = v___x_7153_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7158_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7158_, 0, v_e_7155_);
                        v___x_7157_ = v_reuseFailAlloc_7158_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    leanh::lean_del_object(v___x_7153_);
                    leanh::lean_dec_ref(v_e_7145_);
                    v_e_7159_ = leanh::lean_ctor_get(v_a_7151_, 0);
                    leanh::lean_inc_ref(v_e_7159_);
                    leanh::lean_dec_ref_known(v_a_7151_, 1);
                    v___x_7160_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_7143_, v_post_7144_, v_e_7159_, v_a_7146_, v___y_7147_, v___y_7148_);
                    return v___x_7160_;
                }
                _ => {
                    leanh::lean_dec_ref(v_post_7144_);
                    leanh::lean_dec_ref(v_pre_7143_);
                    v_e_x3f_7161_ = leanh::lean_ctor_get(v_a_7151_, 0);
                    leanh::lean_inc(v_e_x3f_7161_);
                    leanh::lean_dec_ref_known(v_a_7151_, 1);
                    if leanh::lean_obj_tag(v_e_x3f_7161_) == 0 {
                        if v_isShared_7154_ == 0 {
                            leanh::lean_ctor_set(v___x_7153_, 0, v_e_7145_);
                            v___x_7163_ = v___x_7153_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_7164_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7164_, 0, v_e_7145_);
                            v___x_7163_ = v_reuseFailAlloc_7164_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_7145_);
                        v_val_7165_ = leanh::lean_ctor_get(v_e_x3f_7161_, 0);
                        leanh::lean_inc(v_val_7165_);
                        leanh::lean_dec_ref_known(v_e_x3f_7161_, 1);
                        if v_isShared_7154_ == 0 {
                            leanh::lean_ctor_set(v___x_7153_, 0, v_val_7165_);
                            v___x_7167_ = v___x_7153_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_7168_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7168_, 0, v_val_7165_);
                            v___x_7167_ = v_reuseFailAlloc_7168_;
                            state = 4;
                            continue;
                        }
                    }
                }
            },
            2 => {
                return v___x_7157_;
            }
            3 => {
                return v___x_7163_;
            }
            4 => {
                return v___x_7167_;
            }
            5 => {
                if v_isShared_7173_ == 0 {
                    v___x_7175_ = v___x_7172_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7176_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7176_, 0, v_a_7170_);
                    v___x_7175_ = v_reuseFailAlloc_7176_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7175_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2___boxed(
    mut v_pre_7178_: *mut leanh::LeanObject,
    mut v_post_7179_: *mut leanh::LeanObject,
    mut v_e_7180_: *mut leanh::LeanObject,
    mut v_a_7181_: *mut leanh::LeanObject,
    mut v___y_7182_: *mut leanh::LeanObject,
    mut v___y_7183_: *mut leanh::LeanObject,
    mut v___y_7184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7185_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_7178_, v_post_7179_, v_e_7180_, v_a_7181_, v___y_7182_, v___y_7183_);
    leanh::lean_dec(v___y_7183_);
    leanh::lean_dec_ref(v___y_7182_);
    leanh::lean_dec(v_a_7181_);
    return v_res_7185_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1___boxed(
    mut v_pre_7186_: *mut leanh::LeanObject,
    mut v_post_7187_: *mut leanh::LeanObject,
    mut v_sz_7188_: *mut leanh::LeanObject,
    mut v_i_7189_: *mut leanh::LeanObject,
    mut v_bs_7190_: *mut leanh::LeanObject,
    mut v___y_7191_: *mut leanh::LeanObject,
    mut v___y_7192_: *mut leanh::LeanObject,
    mut v___y_7193_: *mut leanh::LeanObject,
    mut v___y_7194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_7195_: usize = 0;
    let mut v_i_boxed_7196_: usize = 0;
    let mut v_res_7197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7195_ = leanh::lean_unbox_usize(v_sz_7188_);
    leanh::lean_dec(v_sz_7188_);
    v_i_boxed_7196_ = leanh::lean_unbox_usize(v_i_7189_);
    leanh::lean_dec(v_i_7189_);
    v_res_7197_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(v_pre_7186_, v_post_7187_, v_sz_boxed_7195_, v_i_boxed_7196_, v_bs_7190_, v___y_7191_, v___y_7192_, v___y_7193_);
    leanh::lean_dec(v___y_7193_);
    leanh::lean_dec_ref(v___y_7192_);
    leanh::lean_dec(v___y_7191_);
    return v_res_7197_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4___boxed(
    mut v_pre_7198_: *mut leanh::LeanObject,
    mut v_post_7199_: *mut leanh::LeanObject,
    mut v_x_7200_: *mut leanh::LeanObject,
    mut v_x_7201_: *mut leanh::LeanObject,
    mut v_x_7202_: *mut leanh::LeanObject,
    mut v___y_7203_: *mut leanh::LeanObject,
    mut v___y_7204_: *mut leanh::LeanObject,
    mut v___y_7205_: *mut leanh::LeanObject,
    mut v___y_7206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7207_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_7198_, v_post_7199_, v_x_7200_, v_x_7201_, v_x_7202_, v___y_7203_, v___y_7204_, v___y_7205_);
    leanh::lean_dec(v___y_7205_);
    leanh::lean_dec_ref(v___y_7204_);
    leanh::lean_dec(v___y_7203_);
    return v_res_7207_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___boxed(
    mut v_pre_7208_: *mut leanh::LeanObject,
    mut v_post_7209_: *mut leanh::LeanObject,
    mut v_e_7210_: *mut leanh::LeanObject,
    mut v_a_7211_: *mut leanh::LeanObject,
    mut v___y_7212_: *mut leanh::LeanObject,
    mut v___y_7213_: *mut leanh::LeanObject,
    mut v___y_7214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7215_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_7208_, v_post_7209_, v_e_7210_, v_a_7211_, v___y_7212_, v___y_7213_);
    leanh::lean_dec(v___y_7213_);
    leanh::lean_dec_ref(v___y_7212_);
    leanh::lean_dec(v_a_7211_);
    return v_res_7215_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(
    mut v_00_u03b1_7216_: *mut leanh::LeanObject,
    mut v_x_7217_: *mut leanh::LeanObject,
    mut v___y_7218_: *mut leanh::LeanObject,
    mut v___y_7219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7221_ = leanh::lean_apply_1(v_x_7217_, leanh::lean_box(0));
    v___x_7222_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_7222_, 0, v___x_7221_);
    return v___x_7222_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0___boxed(
    mut v_00_u03b1_7223_: *mut leanh::LeanObject,
    mut v_x_7224_: *mut leanh::LeanObject,
    mut v___y_7225_: *mut leanh::LeanObject,
    mut v___y_7226_: *mut leanh::LeanObject,
    mut v___y_7227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7228_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(
        v_00_u03b1_7223_,
        v_x_7224_,
        v___y_7225_,
        v___y_7226_,
    );
    leanh::lean_dec(v___y_7226_);
    leanh::lean_dec_ref(v___y_7225_);
    return v_res_7228_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(
    mut v_input_7229_: *mut leanh::LeanObject,
    mut v_pre_7230_: *mut leanh::LeanObject,
    mut v_post_7231_: *mut leanh::LeanObject,
    mut v___y_7232_: *mut leanh::LeanObject,
    mut v___y_7233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7244_: u8 = 0;
    let mut v___x_7246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7248_: u8 = 0;
    let mut v_unused_7249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7235_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Core_transform___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Core_transform___redArg___closed__2_once),
                    _init_l_Lean_Core_transform___redArg___closed__2,
                );
                v___x_7236_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(
                    leanh::lean_box(0),
                    v___x_7235_,
                    v___y_7232_,
                    v___y_7233_,
                );
                v_a_7237_ = leanh::lean_ctor_get(v___x_7236_, 0);
                leanh::lean_inc(v_a_7237_);
                leanh::lean_dec_ref(v___x_7236_);
                v___x_7238_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_7230_, v_post_7231_, v_input_7229_, v_a_7237_, v___y_7232_, v___y_7233_);
                if leanh::lean_obj_tag(v___x_7238_) == 0 {
                    v_a_7239_ = leanh::lean_ctor_get(v___x_7238_, 0);
                    leanh::lean_inc(v_a_7239_);
                    leanh::lean_dec_ref_known(v___x_7238_, 1);
                    v___x_7240_ = leanh::lean_alloc_closure(
                        l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___x_7240_, 0, leanh::lean_box(0));
                    leanh::lean_closure_set(v___x_7240_, 1, leanh::lean_box(0));
                    leanh::lean_closure_set(v___x_7240_, 2, v_a_7237_);
                    v___x_7241_ =
                        l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(
                            leanh::lean_box(0),
                            v___x_7240_,
                            v___y_7232_,
                            v___y_7233_,
                        );
                    v_isSharedCheck_7248_ = (!leanh::lean_is_exclusive(v___x_7241_)) as u8;
                    if v_isSharedCheck_7248_ == 0 {
                        v_unused_7249_ = leanh::lean_ctor_get(v___x_7241_, 0);
                        leanh::lean_dec(v_unused_7249_);
                        v___x_7243_ = v___x_7241_;
                        v_isShared_7244_ = v_isSharedCheck_7248_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_7241_);
                        v___x_7243_ = leanh::lean_box(0);
                        v_isShared_7244_ = v_isSharedCheck_7248_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_7237_);
                    return v___x_7238_;
                }
            }
            1 => {
                if v_isShared_7244_ == 0 {
                    leanh::lean_ctor_set(v___x_7243_, 0, v_a_7239_);
                    v___x_7246_ = v___x_7243_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7247_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7247_, 0, v_a_7239_);
                    v___x_7246_ = v_reuseFailAlloc_7247_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7246_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___boxed(
    mut v_input_7250_: *mut leanh::LeanObject,
    mut v_pre_7251_: *mut leanh::LeanObject,
    mut v_post_7252_: *mut leanh::LeanObject,
    mut v___y_7253_: *mut leanh::LeanObject,
    mut v___y_7254_: *mut leanh::LeanObject,
    mut v___y_7255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7256_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(
        v_input_7250_,
        v_pre_7251_,
        v_post_7252_,
        v___y_7253_,
        v___y_7254_,
    );
    leanh::lean_dec(v___y_7254_);
    leanh::lean_dec_ref(v___y_7253_);
    return v_res_7256_;
}
pub unsafe fn l_Lean_Core_betaReduce(
    mut v_e_7259_: *mut leanh::LeanObject,
    mut v_a_7260_: *mut leanh::LeanObject,
    mut v_a_7261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7265_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7263_ = l_Lean_Core_betaReduce___closed__0;
    v___f_7264_ = l_Lean_Core_betaReduce___closed__1;
    v___x_7265_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(
        v_e_7259_,
        v___f_7263_,
        v___f_7264_,
        v_a_7260_,
        v_a_7261_,
    );
    return v___x_7265_;
}
pub unsafe fn l_Lean_Core_betaReduce___boxed(
    mut v_e_7266_: *mut leanh::LeanObject,
    mut v_a_7267_: *mut leanh::LeanObject,
    mut v_a_7268_: *mut leanh::LeanObject,
    mut v_a_7269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7270_ = l_Lean_Core_betaReduce(v_e_7266_, v_a_7267_, v_a_7268_);
    leanh::lean_dec(v_a_7268_);
    leanh::lean_dec_ref(v_a_7267_);
    return v_res_7270_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(
    mut v_00_u03b2_7271_: *mut leanh::LeanObject,
    mut v_m_7272_: *mut leanh::LeanObject,
    mut v_a_7273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7274_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_m_7272_, v_a_7273_);
    return v___x_7274_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b2_7275_: *mut leanh::LeanObject,
    mut v_m_7276_: *mut leanh::LeanObject,
    mut v_a_7277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7278_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_00_u03b2_7275_, v_m_7276_, v_a_7277_);
    leanh::lean_dec_ref(v_a_7277_);
    leanh::lean_dec_ref(v_m_7276_);
    return v_res_7278_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(
    mut v_00_u03b1_7279_: *mut leanh::LeanObject,
    mut v_ref_7280_: *mut leanh::LeanObject,
    mut v___y_7281_: *mut leanh::LeanObject,
    mut v___y_7282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7284_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_7280_);
    return v___x_7284_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___boxed(
    mut v_00_u03b1_7285_: *mut leanh::LeanObject,
    mut v_ref_7286_: *mut leanh::LeanObject,
    mut v___y_7287_: *mut leanh::LeanObject,
    mut v___y_7288_: *mut leanh::LeanObject,
    mut v___y_7289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7290_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_7285_, v_ref_7286_, v___y_7287_, v___y_7288_);
    leanh::lean_dec(v___y_7288_);
    leanh::lean_dec_ref(v___y_7287_);
    return v_res_7290_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8(
    mut v_00_u03b1_7291_: *mut leanh::LeanObject,
    mut v___y_7292_: *mut leanh::LeanObject,
    mut v___y_7293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7295_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
    return v___x_7295_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___boxed(
    mut v_00_u03b1_7296_: *mut leanh::LeanObject,
    mut v___y_7297_: *mut leanh::LeanObject,
    mut v___y_7298_: *mut leanh::LeanObject,
    mut v___y_7299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7300_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_7296_, v___y_7297_, v___y_7298_);
    leanh::lean_dec(v___y_7298_);
    leanh::lean_dec_ref(v___y_7297_);
    return v_res_7300_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(
    mut v_00_u03b1_7301_: *mut leanh::LeanObject,
    mut v_x_7302_: *mut leanh::LeanObject,
    mut v___y_7303_: *mut leanh::LeanObject,
    mut v___y_7304_: *mut leanh::LeanObject,
    mut v___y_7305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7307_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v_x_7302_, v___y_7303_, v___y_7304_, v___y_7305_);
    return v___x_7307_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___boxed(
    mut v_00_u03b1_7308_: *mut leanh::LeanObject,
    mut v_x_7309_: *mut leanh::LeanObject,
    mut v___y_7310_: *mut leanh::LeanObject,
    mut v___y_7311_: *mut leanh::LeanObject,
    mut v___y_7312_: *mut leanh::LeanObject,
    mut v___y_7313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7314_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(v_00_u03b1_7308_, v_x_7309_, v___y_7310_, v___y_7311_, v___y_7312_);
    leanh::lean_dec(v___y_7312_);
    leanh::lean_dec_ref(v___y_7311_);
    leanh::lean_dec(v___y_7310_);
    return v_res_7314_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6(
    mut v_00_u03b2_7315_: *mut leanh::LeanObject,
    mut v_m_7316_: *mut leanh::LeanObject,
    mut v_a_7317_: *mut leanh::LeanObject,
    mut v_b_7318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7319_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v_m_7316_, v_a_7317_, v_b_7318_);
    return v___x_7319_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(
    mut v_00_u03b2_7320_: *mut leanh::LeanObject,
    mut v_a_7321_: *mut leanh::LeanObject,
    mut v_x_7322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7323_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_7321_, v_x_7322_);
    return v___x_7323_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___boxed(
    mut v_00_u03b2_7324_: *mut leanh::LeanObject,
    mut v_a_7325_: *mut leanh::LeanObject,
    mut v_x_7326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7327_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_7324_, v_a_7325_, v_x_7326_);
    leanh::lean_dec(v_x_7326_);
    leanh::lean_dec_ref(v_a_7325_);
    return v_res_7327_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(
    mut v_00_u03b2_7328_: *mut leanh::LeanObject,
    mut v_a_7329_: *mut leanh::LeanObject,
    mut v_x_7330_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_7331_: u8 = 0;
    v___x_7331_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_7329_, v_x_7330_);
    return v___x_7331_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___boxed(
    mut v_00_u03b2_7332_: *mut leanh::LeanObject,
    mut v_a_7333_: *mut leanh::LeanObject,
    mut v_x_7334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7335_: u8 = 0;
    let mut v_r_7336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7335_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_7332_, v_a_7333_, v_x_7334_);
    leanh::lean_dec(v_x_7334_);
    leanh::lean_dec_ref(v_a_7333_);
    v_r_7336_ = leanh::lean_box((v_res_7335_) as usize);
    return v_r_7336_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11(
    mut v_00_u03b2_7337_: *mut leanh::LeanObject,
    mut v_data_7338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7339_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_data_7338_);
    return v___x_7339_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12(
    mut v_00_u03b2_7340_: *mut leanh::LeanObject,
    mut v_a_7341_: *mut leanh::LeanObject,
    mut v_b_7342_: *mut leanh::LeanObject,
    mut v_x_7343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7344_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_7341_, v_b_7342_, v_x_7343_);
    return v___x_7344_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12(
    mut v_00_u03b2_7345_: *mut leanh::LeanObject,
    mut v_i_7346_: *mut leanh::LeanObject,
    mut v_source_7347_: *mut leanh::LeanObject,
    mut v_target_7348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7349_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_7346_, v_source_7347_, v_target_7348_);
    return v___x_7349_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(
    mut v_00_u03b2_7350_: *mut leanh::LeanObject,
    mut v_x_7351_: *mut leanh::LeanObject,
    mut v_x_7352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7353_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_7351_, v_x_7352_);
    return v___x_7353_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0(
    mut v_toApplicative_7354_: *mut leanh::LeanObject,
    mut v_a_7355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toPure_7356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toPure_7356_ = leanh::lean_ctor_get(v_toApplicative_7354_, 1);
    leanh::lean_inc(v_toPure_7356_);
    leanh::lean_dec_ref(v_toApplicative_7354_);
    v___x_7357_ = leanh::lean_apply_2(v_toPure_7356_, leanh::lean_box(0), v_a_7355_);
    return v___x_7357_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(
    mut v___x_7358_: *mut leanh::LeanObject,
    mut v___y_7359_: *mut leanh::LeanObject,
    mut v___y_7360_: *mut leanh::LeanObject,
    mut v___y_7361_: *mut leanh::LeanObject,
    mut v___y_7362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7364_ = l_Lean_Core_checkSystem(v___x_7358_, v___y_7361_, v___y_7362_);
    return v___x_7364_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13___boxed(
    mut v___x_7365_: *mut leanh::LeanObject,
    mut v___y_7366_: *mut leanh::LeanObject,
    mut v___y_7367_: *mut leanh::LeanObject,
    mut v___y_7368_: *mut leanh::LeanObject,
    mut v___y_7369_: *mut leanh::LeanObject,
    mut v___y_7370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7371_ =
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(
            v___x_7365_,
            v___y_7366_,
            v___y_7367_,
            v___y_7368_,
            v___y_7369_,
        );
    leanh::lean_dec(v___y_7369_);
    leanh::lean_dec_ref(v___y_7368_);
    leanh::lean_dec(v___y_7367_);
    leanh::lean_dec_ref(v___y_7366_);
    return v_res_7371_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(
    mut v_inst_7374_: *mut leanh::LeanObject,
    mut v_x_7375_: *mut leanh::LeanObject,
    mut v___x_7376_: *mut leanh::LeanObject,
    mut v___x_7377_: *mut leanh::LeanObject,
    mut v_inst_7378_: *mut leanh::LeanObject,
    mut v___f_7379_: *mut leanh::LeanObject,
    mut v___x_7380_: *mut leanh::LeanObject,
    mut v___x_7381_: *mut leanh::LeanObject,
    mut v_a_7382_: *mut leanh::LeanObject,
    mut v_toBind_7383_: *mut leanh::LeanObject,
    mut v___f_7384_: *mut leanh::LeanObject,
    mut v_toApplicative_7385_: *mut leanh::LeanObject,
    mut v_a_7386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_a_7386_) == 0 {
        let mut v___f_7387_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7388_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7389_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7390_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3801__overap_7391_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7392_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7393_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_toApplicative_7385_);
        v___f_7387_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___closed__0;
        v___x_7388_ =
            leanh::lean_apply_2(v_inst_7374_, leanh::lean_box(0), v___f_7387_);
        leanh::lean_inc_ref(v___x_7377_);
        leanh::lean_inc_ref(v___x_7376_);
        v___x_7389_ = leanh::lean_alloc_closure(
            l_Lean_MonadCacheT_instMonadLift___aux__1___boxed as *mut core::ffi::c_void,
            10,
            9,
        );
        leanh::lean_closure_set(v___x_7389_, 0, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_7389_, 1, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_7389_, 2, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_7389_, 3, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_7389_, 4, v_x_7375_);
        leanh::lean_closure_set(v___x_7389_, 5, v___x_7376_);
        leanh::lean_closure_set(v___x_7389_, 6, v___x_7377_);
        leanh::lean_closure_set(v___x_7389_, 7, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_7389_, 8, v___x_7388_);
        v___x_7390_ = leanh::lean_alloc_closure(
            l_Lean_MonadCacheT_instMonad___aux__13___boxed as *mut core::ffi::c_void,
            13,
            12,
        );
        leanh::lean_closure_set(v___x_7390_, 0, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_7390_, 1, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_7390_, 2, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_7390_, 3, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_7390_, 4, v_x_7375_);
        leanh::lean_closure_set(v___x_7390_, 5, v___x_7376_);
        leanh::lean_closure_set(v___x_7390_, 6, v___x_7377_);
        leanh::lean_closure_set(v___x_7390_, 7, v_inst_7378_);
        leanh::lean_closure_set(v___x_7390_, 8, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_7390_, 9, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_7390_, 10, v___x_7389_);
        leanh::lean_closure_set(v___x_7390_, 11, v___f_7379_);
        v___x_3801__overap_7391_ =
            l_Lean_Meta_withIncRecDepth___redArg(v___x_7380_, v___x_7381_, v___x_7390_);
        leanh::lean_inc(v_a_7382_);
        v___x_7392_ = leanh::lean_apply_1(v___x_3801__overap_7391_, v_a_7382_);
        v___x_7393_ = leanh::lean_apply_4(
            v_toBind_7383_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_7392_,
            v___f_7384_,
        );
        return v___x_7393_;
    } else {
        let mut v_val_7394_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_7395_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7396_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_7384_);
        leanh::lean_dec(v_toBind_7383_);
        leanh::lean_dec_ref(v___x_7381_);
        leanh::lean_dec_ref(v___x_7380_);
        leanh::lean_dec(v___f_7379_);
        leanh::lean_dec_ref(v_inst_7378_);
        leanh::lean_dec_ref(v___x_7377_);
        leanh::lean_dec_ref(v___x_7376_);
        leanh::lean_dec(v_inst_7374_);
        v_val_7394_ = leanh::lean_ctor_get(v_a_7386_, 0);
        leanh::lean_inc(v_val_7394_);
        leanh::lean_dec_ref_known(v_a_7386_, 1);
        v_toPure_7395_ = leanh::lean_ctor_get(v_toApplicative_7385_, 1);
        leanh::lean_inc(v_toPure_7395_);
        leanh::lean_dec_ref(v_toApplicative_7385_);
        v___x_7396_ =
            leanh::lean_apply_2(v_toPure_7395_, leanh::lean_box(0), v_val_7394_);
        return v___x_7396_;
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed(
    mut v_inst_7397_: *mut leanh::LeanObject,
    mut v_x_7398_: *mut leanh::LeanObject,
    mut v___x_7399_: *mut leanh::LeanObject,
    mut v___x_7400_: *mut leanh::LeanObject,
    mut v_inst_7401_: *mut leanh::LeanObject,
    mut v___f_7402_: *mut leanh::LeanObject,
    mut v___x_7403_: *mut leanh::LeanObject,
    mut v___x_7404_: *mut leanh::LeanObject,
    mut v_a_7405_: *mut leanh::LeanObject,
    mut v_toBind_7406_: *mut leanh::LeanObject,
    mut v___f_7407_: *mut leanh::LeanObject,
    mut v_toApplicative_7408_: *mut leanh::LeanObject,
    mut v_a_7409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7410_ =
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(
            v_inst_7397_,
            v_x_7398_,
            v___x_7399_,
            v___x_7400_,
            v_inst_7401_,
            v___f_7402_,
            v___x_7403_,
            v___x_7404_,
            v_a_7405_,
            v_toBind_7406_,
            v___f_7407_,
            v_toApplicative_7408_,
            v_a_7409_,
        );
    leanh::lean_dec(v_a_7405_);
    return v_res_7410_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(
    mut v___x_7411_: *mut leanh::LeanObject,
    mut v___x_7412_: *mut leanh::LeanObject,
    mut v_declName_7413_: *mut leanh::LeanObject,
    mut v_a_7414_: *mut leanh::LeanObject,
    mut v___f_7415_: *mut leanh::LeanObject,
    mut v_nondep_7416_: u8,
    mut v_a_7417_: *mut leanh::LeanObject,
    mut v_a_7418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7419_: u8 = 0;
    let mut v___x_3820__overap_7420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7419_ = 0;
    v___x_3820__overap_7420_ = l_Lean_Meta_withLetDecl___redArg(
        v___x_7411_,
        v___x_7412_,
        v_declName_7413_,
        v_a_7414_,
        v_a_7418_,
        v___f_7415_,
        v_nondep_7416_,
        v___x_7419_,
    );
    leanh::lean_inc(v_a_7417_);
    v___x_7421_ = leanh::lean_apply_1(v___x_3820__overap_7420_, v_a_7417_);
    return v___x_7421_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed(
    mut v___x_7422_: *mut leanh::LeanObject,
    mut v___x_7423_: *mut leanh::LeanObject,
    mut v_declName_7424_: *mut leanh::LeanObject,
    mut v_a_7425_: *mut leanh::LeanObject,
    mut v___f_7426_: *mut leanh::LeanObject,
    mut v_nondep_7427_: *mut leanh::LeanObject,
    mut v_a_7428_: *mut leanh::LeanObject,
    mut v_a_7429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_nondep_3999__boxed_7430_: u8 = 0;
    let mut v_res_7431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_3999__boxed_7430_ = (leanh::lean_unbox(v_nondep_7427_) as u8);
    v_res_7431_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(v___x_7422_, v___x_7423_, v_declName_7424_, v_a_7425_, v___f_7426_, v_nondep_3999__boxed_7430_, v_a_7428_, v_a_7429_);
    leanh::lean_dec(v_a_7428_);
    return v_res_7431_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(
    mut v_fvars_7432_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7433_: u8,
    mut v_inst_7434_: *mut leanh::LeanObject,
    mut v_toBind_7435_: *mut leanh::LeanObject,
    mut v___f_7436_: *mut leanh::LeanObject,
    mut v_a_7437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7438_: u8 = 0;
    let mut v___x_7439_: u8 = 0;
    let mut v___x_7440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7438_ = 0;
    v___x_7439_ = 1;
    v___x_7440_ = leanh::lean_box((v_usedLetOnly_7433_) as usize);
    v___x_7441_ = leanh::lean_box((v___x_7438_) as usize);
    v___x_7442_ = leanh::lean_box((v___x_7439_) as usize);
    v___x_7443_ = leanh::lean_alloc_closure(
        l_Lean_Meta_mkLetFVars___boxed as *mut core::ffi::c_void,
        10,
        5,
    );
    leanh::lean_closure_set(v___x_7443_, 0, v_fvars_7432_);
    leanh::lean_closure_set(v___x_7443_, 1, v_a_7437_);
    leanh::lean_closure_set(v___x_7443_, 2, v___x_7440_);
    leanh::lean_closure_set(v___x_7443_, 3, v___x_7441_);
    leanh::lean_closure_set(v___x_7443_, 4, v___x_7442_);
    v___x_7444_ = leanh::lean_apply_2(v_inst_7434_, leanh::lean_box(0), v___x_7443_);
    v___x_7445_ = leanh::lean_apply_4(
        v_toBind_7435_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_7444_,
        v___f_7436_,
    );
    return v___x_7445_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed(
    mut v_fvars_7446_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7447_: *mut leanh::LeanObject,
    mut v_inst_7448_: *mut leanh::LeanObject,
    mut v_toBind_7449_: *mut leanh::LeanObject,
    mut v___f_7450_: *mut leanh::LeanObject,
    mut v_a_7451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7452_: u8 = 0;
    let mut v_res_7453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7452_ = (leanh::lean_unbox(v_usedLetOnly_7447_) as u8);
    v_res_7453_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(v_fvars_7446_, v_usedLetOnly_boxed_7452_, v_inst_7448_, v_toBind_7449_, v___f_7450_, v_a_7451_);
    return v_res_7453_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(
    mut v_fvars_7454_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7455_: u8,
    mut v_inst_7456_: *mut leanh::LeanObject,
    mut v_toBind_7457_: *mut leanh::LeanObject,
    mut v___f_7458_: *mut leanh::LeanObject,
    mut v_a_7459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7460_: u8 = 0;
    let mut v___x_7461_: u8 = 0;
    let mut v___x_7462_: u8 = 0;
    let mut v___x_7463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7460_ = 0;
    v___x_7461_ = 1;
    v___x_7462_ = 1;
    v___x_7463_ = leanh::lean_box((v___x_7460_) as usize);
    v___x_7464_ = leanh::lean_box((v_usedLetOnly_7455_) as usize);
    v___x_7465_ = leanh::lean_box((v___x_7460_) as usize);
    v___x_7466_ = leanh::lean_box((v___x_7461_) as usize);
    v___x_7467_ = leanh::lean_box((v___x_7462_) as usize);
    v___x_7468_ = leanh::lean_alloc_closure(
        l_Lean_Meta_mkLambdaFVars___boxed as *mut core::ffi::c_void,
        12,
        7,
    );
    leanh::lean_closure_set(v___x_7468_, 0, v_fvars_7454_);
    leanh::lean_closure_set(v___x_7468_, 1, v_a_7459_);
    leanh::lean_closure_set(v___x_7468_, 2, v___x_7463_);
    leanh::lean_closure_set(v___x_7468_, 3, v___x_7464_);
    leanh::lean_closure_set(v___x_7468_, 4, v___x_7465_);
    leanh::lean_closure_set(v___x_7468_, 5, v___x_7466_);
    leanh::lean_closure_set(v___x_7468_, 6, v___x_7467_);
    v___x_7469_ = leanh::lean_apply_2(v_inst_7456_, leanh::lean_box(0), v___x_7468_);
    v___x_7470_ = leanh::lean_apply_4(
        v_toBind_7457_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_7469_,
        v___f_7458_,
    );
    return v___x_7470_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed(
    mut v_fvars_7471_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7472_: *mut leanh::LeanObject,
    mut v_inst_7473_: *mut leanh::LeanObject,
    mut v_toBind_7474_: *mut leanh::LeanObject,
    mut v___f_7475_: *mut leanh::LeanObject,
    mut v_a_7476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7477_: u8 = 0;
    let mut v_res_7478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7477_ = (leanh::lean_unbox(v_usedLetOnly_7472_) as u8);
    v_res_7478_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(v_fvars_7471_, v_usedLetOnly_boxed_7477_, v_inst_7473_, v_toBind_7474_, v___f_7475_, v_a_7476_);
    return v_res_7478_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(
    mut v___x_7479_: *mut leanh::LeanObject,
    mut v___x_7480_: *mut leanh::LeanObject,
    mut v_binderName_7481_: *mut leanh::LeanObject,
    mut v_binderInfo_7482_: u8,
    mut v___f_7483_: *mut leanh::LeanObject,
    mut v_a_7484_: *mut leanh::LeanObject,
    mut v_a_7485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7486_: u8 = 0;
    let mut v___x_3878__overap_7487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7486_ = 0;
    v___x_3878__overap_7487_ = l_Lean_Meta_withLocalDecl___redArg(
        v___x_7479_,
        v___x_7480_,
        v_binderName_7481_,
        v_binderInfo_7482_,
        v_a_7485_,
        v___f_7483_,
        v___x_7486_,
    );
    leanh::lean_inc(v_a_7484_);
    v___x_7488_ = leanh::lean_apply_1(v___x_3878__overap_7487_, v_a_7484_);
    return v___x_7488_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed(
    mut v___x_7489_: *mut leanh::LeanObject,
    mut v___x_7490_: *mut leanh::LeanObject,
    mut v_binderName_7491_: *mut leanh::LeanObject,
    mut v_binderInfo_7492_: *mut leanh::LeanObject,
    mut v___f_7493_: *mut leanh::LeanObject,
    mut v_a_7494_: *mut leanh::LeanObject,
    mut v_a_7495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_binderInfo_4067__boxed_7496_: u8 = 0;
    let mut v_res_7497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_binderInfo_4067__boxed_7496_ = (leanh::lean_unbox(v_binderInfo_7492_) as u8);
    v_res_7497_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(v___x_7489_, v___x_7490_, v_binderName_7491_, v_binderInfo_4067__boxed_7496_, v___f_7493_, v_a_7494_, v_a_7495_);
    leanh::lean_dec(v_a_7494_);
    return v_res_7497_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(
    mut v_fvars_7498_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7499_: u8,
    mut v_inst_7500_: *mut leanh::LeanObject,
    mut v_toBind_7501_: *mut leanh::LeanObject,
    mut v___f_7502_: *mut leanh::LeanObject,
    mut v_a_7503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7504_: u8 = 0;
    let mut v___x_7505_: u8 = 0;
    let mut v___x_7506_: u8 = 0;
    let mut v___x_7507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7504_ = 0;
    v___x_7505_ = 1;
    v___x_7506_ = 1;
    v___x_7507_ = leanh::lean_box((v___x_7504_) as usize);
    v___x_7508_ = leanh::lean_box((v_usedLetOnly_7499_) as usize);
    v___x_7509_ = leanh::lean_box((v___x_7505_) as usize);
    v___x_7510_ = leanh::lean_box((v___x_7506_) as usize);
    v___x_7511_ = leanh::lean_alloc_closure(
        l_Lean_Meta_mkForallFVars___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    leanh::lean_closure_set(v___x_7511_, 0, v_fvars_7498_);
    leanh::lean_closure_set(v___x_7511_, 1, v_a_7503_);
    leanh::lean_closure_set(v___x_7511_, 2, v___x_7507_);
    leanh::lean_closure_set(v___x_7511_, 3, v___x_7508_);
    leanh::lean_closure_set(v___x_7511_, 4, v___x_7509_);
    leanh::lean_closure_set(v___x_7511_, 5, v___x_7510_);
    v___x_7512_ = leanh::lean_apply_2(v_inst_7500_, leanh::lean_box(0), v___x_7511_);
    v___x_7513_ = leanh::lean_apply_4(
        v_toBind_7501_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_7512_,
        v___f_7502_,
    );
    return v___x_7513_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed(
    mut v_fvars_7514_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7515_: *mut leanh::LeanObject,
    mut v_inst_7516_: *mut leanh::LeanObject,
    mut v_toBind_7517_: *mut leanh::LeanObject,
    mut v___f_7518_: *mut leanh::LeanObject,
    mut v_a_7519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7520_: u8 = 0;
    let mut v_res_7521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7520_ = (leanh::lean_unbox(v_usedLetOnly_7515_) as u8);
    v_res_7521_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(v_fvars_7514_, v_usedLetOnly_boxed_7520_, v_inst_7516_, v_toBind_7517_, v___f_7518_, v_a_7519_);
    return v_res_7521_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(
    mut v___f_7522_: *mut leanh::LeanObject,
    mut v___y_7523_: *mut leanh::LeanObject,
    mut v_a_7524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7525_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_7523_);
    v___x_7525_ = leanh::lean_apply_2(v___f_7522_, v_a_7524_, v___y_7523_);
    return v___x_7525_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed(
    mut v___f_7526_: *mut leanh::LeanObject,
    mut v___y_7527_: *mut leanh::LeanObject,
    mut v_a_7528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7529_ =
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(
            v___f_7526_,
            v___y_7527_,
            v_a_7528_,
        );
    leanh::lean_dec(v___y_7527_);
    return v_res_7529_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(
    mut v_toApplicative_7530_: *mut leanh::LeanObject,
    mut v_acc_7531_: *mut leanh::LeanObject,
    mut v_next_7532_: *mut leanh::LeanObject,
    mut v_a_7533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toPure_7534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toPure_7534_ = leanh::lean_ctor_get(v_toApplicative_7530_, 1);
    leanh::lean_inc(v_toPure_7534_);
    leanh::lean_dec_ref(v_toApplicative_7530_);
    v___x_7535_ = lean_array_fset(v_acc_7531_, v_next_7532_, v_a_7533_);
    v___x_7536_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_7536_, 0, v___x_7535_);
    v___x_7537_ =
        leanh::lean_apply_2(v_toPure_7534_, leanh::lean_box(0), v___x_7536_);
    return v___x_7537_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed(
    mut v_toApplicative_7538_: *mut leanh::LeanObject,
    mut v_acc_7539_: *mut leanh::LeanObject,
    mut v_next_7540_: *mut leanh::LeanObject,
    mut v_a_7541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7542_ =
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(
            v_toApplicative_7538_,
            v_acc_7539_,
            v_next_7540_,
            v_a_7541_,
        );
    leanh::lean_dec(v_next_7540_);
    return v_res_7542_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(
    mut v_toApplicative_7543_: *mut leanh::LeanObject,
    mut v_next_7544_: *mut leanh::LeanObject,
    mut v_G_7545_: *mut leanh::LeanObject,
    mut v___y_7546_: *mut leanh::LeanObject,
    mut v_a_7547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_a_7547_) == 0 {
        let mut v_a_7548_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_7549_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7550_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_G_7545_);
        v_a_7548_ = leanh::lean_ctor_get(v_a_7547_, 0);
        leanh::lean_inc(v_a_7548_);
        leanh::lean_dec_ref_known(v_a_7547_, 1);
        v_toPure_7549_ = leanh::lean_ctor_get(v_toApplicative_7543_, 1);
        leanh::lean_inc(v_toPure_7549_);
        leanh::lean_dec_ref(v_toApplicative_7543_);
        v___x_7550_ =
            leanh::lean_apply_2(v_toPure_7549_, leanh::lean_box(0), v_a_7548_);
        return v___x_7550_;
    } else {
        let mut v_a_7551_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7552_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7553_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7554_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_toApplicative_7543_);
        v_a_7551_ = leanh::lean_ctor_get(v_a_7547_, 0);
        leanh::lean_inc(v_a_7551_);
        leanh::lean_dec_ref_known(v_a_7547_, 1);
        v___x_7552_ = leanh::lean_unsigned_to_nat(1);
        v___x_7553_ = lean_nat_add(v_next_7544_, v___x_7552_);
        leanh::lean_inc(v___y_7546_);
        v___x_7554_ = leanh::lean_apply_5(
            v_G_7545_,
            v___x_7553_,
            v_a_7551_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___y_7546_,
        );
        return v___x_7554_;
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed(
    mut v_toApplicative_7555_: *mut leanh::LeanObject,
    mut v_next_7556_: *mut leanh::LeanObject,
    mut v_G_7557_: *mut leanh::LeanObject,
    mut v___y_7558_: *mut leanh::LeanObject,
    mut v_a_7559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7560_ =
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(
            v_toApplicative_7555_,
            v_next_7556_,
            v_G_7557_,
            v___y_7558_,
            v_a_7559_,
        );
    leanh::lean_dec(v___y_7558_);
    leanh::lean_dec(v_next_7556_);
    return v_res_7560_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(
    mut v_f_7561_: *mut leanh::LeanObject,
    mut v_inst_7562_: *mut leanh::LeanObject,
    mut v_inst_7563_: *mut leanh::LeanObject,
    mut v_inst_7564_: *mut leanh::LeanObject,
    mut v_pre_7565_: *mut leanh::LeanObject,
    mut v_post_7566_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7567_: u8,
    mut v_skipConstInApp_7568_: u8,
    mut v_skipInstances_7569_: u8,
    mut v_x_7570_: *mut leanh::LeanObject,
    mut v_x_7571_: *mut leanh::LeanObject,
    mut v___y_7572_: *mut leanh::LeanObject,
    mut v_a_7573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7574_ = l_Lean_mkAppN(v_f_7561_, v_a_7573_);
    v___x_7575_ =
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(
            v_inst_7562_,
            v_inst_7563_,
            v_inst_7564_,
            v_pre_7565_,
            v_post_7566_,
            v_usedLetOnly_7567_,
            v_skipConstInApp_7568_,
            v_skipInstances_7569_,
            v_x_7570_,
            v_x_7571_,
            v___x_7574_,
            v___y_7572_,
        );
    return v___x_7575_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed(
    mut v_f_7576_: *mut leanh::LeanObject,
    mut v_inst_7577_: *mut leanh::LeanObject,
    mut v_inst_7578_: *mut leanh::LeanObject,
    mut v_inst_7579_: *mut leanh::LeanObject,
    mut v_pre_7580_: *mut leanh::LeanObject,
    mut v_post_7581_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7582_: *mut leanh::LeanObject,
    mut v_skipConstInApp_7583_: *mut leanh::LeanObject,
    mut v_skipInstances_7584_: *mut leanh::LeanObject,
    mut v_x_7585_: *mut leanh::LeanObject,
    mut v_x_7586_: *mut leanh::LeanObject,
    mut v___y_7587_: *mut leanh::LeanObject,
    mut v_a_7588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7589_: u8 = 0;
    let mut v_skipConstInApp_boxed_7590_: u8 = 0;
    let mut v_skipInstances_boxed_7591_: u8 = 0;
    let mut v_res_7592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7589_ = (leanh::lean_unbox(v_usedLetOnly_7582_) as u8);
    v_skipConstInApp_boxed_7590_ = (leanh::lean_unbox(v_skipConstInApp_7583_) as u8);
    v_skipInstances_boxed_7591_ = (leanh::lean_unbox(v_skipInstances_7584_) as u8);
    v_res_7592_ =
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(
            v_f_7576_,
            v_inst_7577_,
            v_inst_7578_,
            v_inst_7579_,
            v_pre_7580_,
            v_post_7581_,
            v_usedLetOnly_boxed_7589_,
            v_skipConstInApp_boxed_7590_,
            v_skipInstances_boxed_7591_,
            v_x_7585_,
            v_x_7586_,
            v___y_7587_,
            v_a_7588_,
        );
    leanh::lean_dec_ref(v_a_7588_);
    leanh::lean_dec(v___y_7587_);
    return v_res_7592_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed(
    mut v_inst_7593_: *mut leanh::LeanObject,
    mut v_inst_7594_: *mut leanh::LeanObject,
    mut v_inst_7595_: *mut leanh::LeanObject,
    mut v_pre_7596_: *mut leanh::LeanObject,
    mut v_post_7597_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7598_: *mut leanh::LeanObject,
    mut v_skipConstInApp_7599_: *mut leanh::LeanObject,
    mut v_skipInstances_7600_: *mut leanh::LeanObject,
    mut v_x_7601_: *mut leanh::LeanObject,
    mut v_x_7602_: *mut leanh::LeanObject,
    mut v_e_7603_: *mut leanh::LeanObject,
    mut v_a_7604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7605_: u8 = 0;
    let mut v_skipConstInApp_boxed_7606_: u8 = 0;
    let mut v_skipInstances_boxed_7607_: u8 = 0;
    let mut v_res_7608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7605_ = (leanh::lean_unbox(v_usedLetOnly_7598_) as u8);
    v_skipConstInApp_boxed_7606_ = (leanh::lean_unbox(v_skipConstInApp_7599_) as u8);
    v_skipInstances_boxed_7607_ = (leanh::lean_unbox(v_skipInstances_7600_) as u8);
    v_res_7608_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(
        v_inst_7593_,
        v_inst_7594_,
        v_inst_7595_,
        v_pre_7596_,
        v_post_7597_,
        v_usedLetOnly_boxed_7605_,
        v_skipConstInApp_boxed_7606_,
        v_skipInstances_boxed_7607_,
        v_x_7601_,
        v_x_7602_,
        v_e_7603_,
        v_a_7604_,
    );
    leanh::lean_dec(v_a_7604_);
    return v_res_7608_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(
    mut v___x_7609_: *mut leanh::LeanObject,
    mut v_toApplicative_7610_: *mut leanh::LeanObject,
    mut v_toBind_7611_: *mut leanh::LeanObject,
    mut v___f_7612_: *mut leanh::LeanObject,
    mut v_paramInfo_7613_: *mut leanh::LeanObject,
    mut v_inst_7614_: *mut leanh::LeanObject,
    mut v_inst_7615_: *mut leanh::LeanObject,
    mut v_inst_7616_: *mut leanh::LeanObject,
    mut v_pre_7617_: *mut leanh::LeanObject,
    mut v_post_7618_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7619_: u8,
    mut v_skipConstInApp_7620_: u8,
    mut v_skipInstances_7621_: u8,
    mut v_x_7622_: *mut leanh::LeanObject,
    mut v_x_7623_: *mut leanh::LeanObject,
    mut v_next_7624_: *mut leanh::LeanObject,
    mut v_acc_7625_: *mut leanh::LeanObject,
    mut v_h_7626_: *mut leanh::LeanObject,
    mut v_G_7627_: *mut leanh::LeanObject,
    mut v___y_7628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7629_: u8 = 0;
    let mut v_toPure_7630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7639_: u8 = 0;
    let mut v___f_7640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInstance_7644_: u8 = 0;
    let mut v___f_7645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_7648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7629_ = lean_nat_dec_lt(v_next_7624_, v___x_7609_);
                if v___x_7629_ == 0 {
                    leanh::lean_dec(v_G_7627_);
                    leanh::lean_dec(v_next_7624_);
                    leanh::lean_dec(v_x_7623_);
                    leanh::lean_dec(v_post_7618_);
                    leanh::lean_dec(v_pre_7617_);
                    leanh::lean_dec_ref(v_inst_7616_);
                    leanh::lean_dec(v_inst_7615_);
                    leanh::lean_dec_ref(v_inst_7614_);
                    leanh::lean_dec(v___f_7612_);
                    leanh::lean_dec(v_toBind_7611_);
                    v_toPure_7630_ = leanh::lean_ctor_get(v_toApplicative_7610_, 1);
                    leanh::lean_inc(v_toPure_7630_);
                    leanh::lean_dec_ref(v_toApplicative_7610_);
                    v___x_7631_ = leanh::lean_apply_2(
                        v_toPure_7630_,
                        leanh::lean_box(0),
                        v_acc_7625_,
                    );
                    return v___x_7631_;
                } else {
                    leanh::lean_inc(v___y_7628_);
                    leanh::lean_inc(v_next_7624_);
                    leanh::lean_inc_ref(v_toApplicative_7610_);
                    v___f_7632_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed as *mut core::ffi::c_void, 5, 4);
                    leanh::lean_closure_set(v___f_7632_, 0, v_toApplicative_7610_);
                    leanh::lean_closure_set(v___f_7632_, 1, v_next_7624_);
                    leanh::lean_closure_set(v___f_7632_, 2, v_G_7627_);
                    leanh::lean_closure_set(v___f_7632_, 3, v___y_7628_);
                    v___x_7637_ = lean_array_fget_borrowed(v_acc_7625_, v_next_7624_);
                    v___x_7638_ = lean_array_get_size(v_paramInfo_7613_);
                    v___x_7639_ = lean_nat_dec_lt(v_next_7624_, v___x_7638_);
                    if v___x_7639_ == 0 {
                        leanh::lean_inc(v___x_7637_);
                        v___f_7640_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 3);
                        leanh::lean_closure_set(v___f_7640_, 0, v_toApplicative_7610_);
                        leanh::lean_closure_set(v___f_7640_, 1, v_acc_7625_);
                        leanh::lean_closure_set(v___f_7640_, 2, v_next_7624_);
                        v___x_7641_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_7614_, v_inst_7615_, v_inst_7616_, v_pre_7617_, v_post_7618_, v_usedLetOnly_7619_, v_skipConstInApp_7620_, v_skipInstances_7621_, v_x_7622_, v_x_7623_, v___x_7637_, v___y_7628_);
                        leanh::lean_inc(v_toBind_7611_);
                        v___x_7642_ = leanh::lean_apply_4(
                            v_toBind_7611_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_7641_,
                            v___f_7640_,
                        );
                        v___y_7634_ = v___x_7642_;
                        state = 1;
                        continue;
                    } else {
                        v___x_7643_ = lean_array_fget_borrowed(v_paramInfo_7613_, v_next_7624_);
                        v_isInstance_7644_ = leanh::lean_ctor_get_uint8(
                            v___x_7643_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 4) as u32,
                        );
                        if v_isInstance_7644_ == 0 {
                            leanh::lean_inc(v___x_7637_);
                            v___f_7645_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 3);
                            leanh::lean_closure_set(v___f_7645_, 0, v_toApplicative_7610_);
                            leanh::lean_closure_set(v___f_7645_, 1, v_acc_7625_);
                            leanh::lean_closure_set(v___f_7645_, 2, v_next_7624_);
                            v___x_7646_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_7614_, v_inst_7615_, v_inst_7616_, v_pre_7617_, v_post_7618_, v_usedLetOnly_7619_, v_skipConstInApp_7620_, v_skipInstances_7621_, v_x_7622_, v_x_7623_, v___x_7637_, v___y_7628_);
                            leanh::lean_inc(v_toBind_7611_);
                            v___x_7647_ = leanh::lean_apply_4(
                                v_toBind_7611_,
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v___x_7646_,
                                v___f_7645_,
                            );
                            v___y_7634_ = v___x_7647_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_next_7624_);
                            leanh::lean_dec(v_x_7623_);
                            leanh::lean_dec(v_post_7618_);
                            leanh::lean_dec(v_pre_7617_);
                            leanh::lean_dec_ref(v_inst_7616_);
                            leanh::lean_dec(v_inst_7615_);
                            leanh::lean_dec_ref(v_inst_7614_);
                            v_toPure_7648_ = leanh::lean_ctor_get(v_toApplicative_7610_, 1);
                            leanh::lean_inc(v_toPure_7648_);
                            leanh::lean_dec_ref(v_toApplicative_7610_);
                            v___x_7649_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_7649_, 0, v_acc_7625_);
                            v___x_7650_ = leanh::lean_apply_2(
                                v_toPure_7648_,
                                leanh::lean_box(0),
                                v___x_7649_,
                            );
                            v___y_7634_ = v___x_7650_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_toBind_7611_);
                v___x_7635_ = leanh::lean_apply_4(
                    v_toBind_7611_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___y_7634_,
                    v___f_7612_,
                );
                v___x_7636_ = leanh::lean_apply_4(
                    v_toBind_7611_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_7635_,
                    v___f_7632_,
                );
                return v___x_7636_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7651_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_toApplicative_7652_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_toBind_7653_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___f_7654_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_paramInfo_7655_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_inst_7656_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_inst_7657_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_inst_7658_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_pre_7659_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_post_7660_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_usedLetOnly_7661_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_skipConstInApp_7662_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_skipInstances_7663_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_x_7664_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_x_7665_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_next_7666_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_acc_7667_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_h_7668_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_G_7669_: *mut leanh::LeanObject = *_args.add(18);
    let mut v___y_7670_: *mut leanh::LeanObject = *_args.add(19);
    let mut v_usedLetOnly_boxed_7671_: u8 = 0;
    let mut v_skipConstInApp_boxed_7672_: u8 = 0;
    let mut v_skipInstances_boxed_7673_: u8 = 0;
    let mut v_res_7674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7671_ = (leanh::lean_unbox(v_usedLetOnly_7661_) as u8);
    v_skipConstInApp_boxed_7672_ = (leanh::lean_unbox(v_skipConstInApp_7662_) as u8);
    v_skipInstances_boxed_7673_ = (leanh::lean_unbox(v_skipInstances_7663_) as u8);
    v_res_7674_ =
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(
            v___x_7651_,
            v_toApplicative_7652_,
            v_toBind_7653_,
            v___f_7654_,
            v_paramInfo_7655_,
            v_inst_7656_,
            v_inst_7657_,
            v_inst_7658_,
            v_pre_7659_,
            v_post_7660_,
            v_usedLetOnly_boxed_7671_,
            v_skipConstInApp_boxed_7672_,
            v_skipInstances_boxed_7673_,
            v_x_7664_,
            v_x_7665_,
            v_next_7666_,
            v_acc_7667_,
            v_h_7668_,
            v_G_7669_,
            v___y_7670_,
        );
    leanh::lean_dec(v___y_7670_);
    leanh::lean_dec_ref(v_paramInfo_7655_);
    leanh::lean_dec(v___x_7651_);
    return v_res_7674_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(
    mut v___x_7675_: *mut leanh::LeanObject,
    mut v_toApplicative_7676_: *mut leanh::LeanObject,
    mut v_toBind_7677_: *mut leanh::LeanObject,
    mut v___f_7678_: *mut leanh::LeanObject,
    mut v_inst_7679_: *mut leanh::LeanObject,
    mut v_inst_7680_: *mut leanh::LeanObject,
    mut v_inst_7681_: *mut leanh::LeanObject,
    mut v_pre_7682_: *mut leanh::LeanObject,
    mut v_post_7683_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7684_: u8,
    mut v_skipConstInApp_7685_: u8,
    mut v_skipInstances_7686_: u8,
    mut v_x_7687_: *mut leanh::LeanObject,
    mut v_x_7688_: *mut leanh::LeanObject,
    mut v_args_7689_: *mut leanh::LeanObject,
    mut v___y_7690_: *mut leanh::LeanObject,
    mut v___f_7691_: *mut leanh::LeanObject,
    mut v_a_7692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_paramInfo_7693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638__overap_7699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_paramInfo_7693_ = leanh::lean_ctor_get(v_a_7692_, 0);
    leanh::lean_inc_ref(v_paramInfo_7693_);
    leanh::lean_dec_ref(v_a_7692_);
    v___x_7694_ = leanh::lean_unsigned_to_nat(0);
    v___x_7695_ = leanh::lean_box((v_usedLetOnly_7684_) as usize);
    v___x_7696_ = leanh::lean_box((v_skipConstInApp_7685_) as usize);
    v___x_7697_ = leanh::lean_box((v_skipInstances_7686_) as usize);
    leanh::lean_inc(v_toBind_7677_);
    v___f_7698_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed as *mut core::ffi::c_void, 20, 15);
    leanh::lean_closure_set(v___f_7698_, 0, v___x_7675_);
    leanh::lean_closure_set(v___f_7698_, 1, v_toApplicative_7676_);
    leanh::lean_closure_set(v___f_7698_, 2, v_toBind_7677_);
    leanh::lean_closure_set(v___f_7698_, 3, v___f_7678_);
    leanh::lean_closure_set(v___f_7698_, 4, v_paramInfo_7693_);
    leanh::lean_closure_set(v___f_7698_, 5, v_inst_7679_);
    leanh::lean_closure_set(v___f_7698_, 6, v_inst_7680_);
    leanh::lean_closure_set(v___f_7698_, 7, v_inst_7681_);
    leanh::lean_closure_set(v___f_7698_, 8, v_pre_7682_);
    leanh::lean_closure_set(v___f_7698_, 9, v_post_7683_);
    leanh::lean_closure_set(v___f_7698_, 10, v___x_7695_);
    leanh::lean_closure_set(v___f_7698_, 11, v___x_7696_);
    leanh::lean_closure_set(v___f_7698_, 12, v___x_7697_);
    leanh::lean_closure_set(v___f_7698_, 13, v_x_7687_);
    leanh::lean_closure_set(v___f_7698_, 14, v_x_7688_);
    v___x_3638__overap_7699_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_7698_,
        v___x_7694_,
        v_args_7689_,
        leanh::lean_box(0),
    );
    leanh::lean_inc(v___y_7690_);
    v___x_7700_ = leanh::lean_apply_1(v___x_3638__overap_7699_, v___y_7690_);
    v___x_7701_ = leanh::lean_apply_4(
        v_toBind_7677_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_7700_,
        v___f_7691_,
    );
    return v___x_7701_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7702_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_toApplicative_7703_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_toBind_7704_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___f_7705_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_inst_7706_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_inst_7707_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_inst_7708_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_pre_7709_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_post_7710_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_usedLetOnly_7711_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_skipConstInApp_7712_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_skipInstances_7713_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_x_7714_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_x_7715_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_args_7716_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_7717_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___f_7718_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_a_7719_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_usedLetOnly_boxed_7720_: u8 = 0;
    let mut v_skipConstInApp_boxed_7721_: u8 = 0;
    let mut v_skipInstances_boxed_7722_: u8 = 0;
    let mut v_res_7723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7720_ = (leanh::lean_unbox(v_usedLetOnly_7711_) as u8);
    v_skipConstInApp_boxed_7721_ = (leanh::lean_unbox(v_skipConstInApp_7712_) as u8);
    v_skipInstances_boxed_7722_ = (leanh::lean_unbox(v_skipInstances_7713_) as u8);
    v_res_7723_ =
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(
            v___x_7702_,
            v_toApplicative_7703_,
            v_toBind_7704_,
            v___f_7705_,
            v_inst_7706_,
            v_inst_7707_,
            v_inst_7708_,
            v_pre_7709_,
            v_post_7710_,
            v_usedLetOnly_boxed_7720_,
            v_skipConstInApp_boxed_7721_,
            v_skipInstances_boxed_7722_,
            v_x_7714_,
            v_x_7715_,
            v_args_7716_,
            v___y_7717_,
            v___f_7718_,
            v_a_7719_,
        );
    leanh::lean_dec(v___y_7717_);
    return v_res_7723_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(
    mut v_skipInstances_7724_: u8,
    mut v_inst_7725_: *mut leanh::LeanObject,
    mut v_inst_7726_: *mut leanh::LeanObject,
    mut v_inst_7727_: *mut leanh::LeanObject,
    mut v_pre_7728_: *mut leanh::LeanObject,
    mut v_post_7729_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7730_: u8,
    mut v_skipConstInApp_7731_: u8,
    mut v_x_7732_: *mut leanh::LeanObject,
    mut v_x_7733_: *mut leanh::LeanObject,
    mut v_args_7734_: *mut leanh::LeanObject,
    mut v___x_7735_: *mut leanh::LeanObject,
    mut v_toBind_7736_: *mut leanh::LeanObject,
    mut v_toApplicative_7737_: *mut leanh::LeanObject,
    mut v___f_7738_: *mut leanh::LeanObject,
    mut v_f_7739_: *mut leanh::LeanObject,
    mut v___y_7740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_skipInstances_7724_ == 0 {
        let mut v___x_7741_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7742_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7743_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_7744_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7745_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7746_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7747_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7748_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_7749_: usize = 0;
        let mut v___x_7750_: usize = 0;
        let mut v___x_3651__overap_7751_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7752_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7753_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_7738_);
        leanh::lean_dec_ref(v_toApplicative_7737_);
        v___x_7741_ = leanh::lean_box((v_usedLetOnly_7730_) as usize);
        v___x_7742_ = leanh::lean_box((v_skipConstInApp_7731_) as usize);
        v___x_7743_ = leanh::lean_box((v_skipInstances_7724_) as usize);
        leanh::lean_inc_n(v___y_7740_, 2);
        leanh::lean_inc(v_x_7733_);
        leanh::lean_inc(v_post_7729_);
        leanh::lean_inc(v_pre_7728_);
        leanh::lean_inc_ref(v_inst_7727_);
        leanh::lean_inc(v_inst_7726_);
        leanh::lean_inc_ref(v_inst_7725_);
        v___f_7744_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed as *mut core::ffi::c_void, 13, 12);
        leanh::lean_closure_set(v___f_7744_, 0, v_f_7739_);
        leanh::lean_closure_set(v___f_7744_, 1, v_inst_7725_);
        leanh::lean_closure_set(v___f_7744_, 2, v_inst_7726_);
        leanh::lean_closure_set(v___f_7744_, 3, v_inst_7727_);
        leanh::lean_closure_set(v___f_7744_, 4, v_pre_7728_);
        leanh::lean_closure_set(v___f_7744_, 5, v_post_7729_);
        leanh::lean_closure_set(v___f_7744_, 6, v___x_7741_);
        leanh::lean_closure_set(v___f_7744_, 7, v___x_7742_);
        leanh::lean_closure_set(v___f_7744_, 8, v___x_7743_);
        leanh::lean_closure_set(v___f_7744_, 9, v_x_7732_);
        leanh::lean_closure_set(v___f_7744_, 10, v_x_7733_);
        leanh::lean_closure_set(v___f_7744_, 11, v___y_7740_);
        v___x_7745_ = leanh::lean_box((v_usedLetOnly_7730_) as usize);
        v___x_7746_ = leanh::lean_box((v_skipConstInApp_7731_) as usize);
        v___x_7747_ = leanh::lean_box((v_skipInstances_7724_) as usize);
        v___x_7748_ = leanh::lean_alloc_closure(
            l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed
                as *mut core::ffi::c_void,
            12,
            10,
        );
        leanh::lean_closure_set(v___x_7748_, 0, v_inst_7725_);
        leanh::lean_closure_set(v___x_7748_, 1, v_inst_7726_);
        leanh::lean_closure_set(v___x_7748_, 2, v_inst_7727_);
        leanh::lean_closure_set(v___x_7748_, 3, v_pre_7728_);
        leanh::lean_closure_set(v___x_7748_, 4, v_post_7729_);
        leanh::lean_closure_set(v___x_7748_, 5, v___x_7745_);
        leanh::lean_closure_set(v___x_7748_, 6, v___x_7746_);
        leanh::lean_closure_set(v___x_7748_, 7, v___x_7747_);
        leanh::lean_closure_set(v___x_7748_, 8, v_x_7732_);
        leanh::lean_closure_set(v___x_7748_, 9, v_x_7733_);
        v_sz_7749_ = lean_array_size(v_args_7734_);
        v___x_7750_ = 0usize;
        v___x_3651__overap_7751_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_7735_,
            v___x_7748_,
            v_sz_7749_,
            v___x_7750_,
            v_args_7734_,
        );
        v___x_7752_ = leanh::lean_apply_1(v___x_3651__overap_7751_, v___y_7740_);
        v___x_7753_ = leanh::lean_apply_4(
            v_toBind_7736_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_7752_,
            v___f_7744_,
        );
        return v___x_7753_;
    } else {
        let mut v___x_7754_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7755_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7756_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_7757_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7758_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7759_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7760_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7761_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_7762_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7763_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7764_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7765_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_7735_);
        v___x_7754_ = leanh::lean_box((v_usedLetOnly_7730_) as usize);
        v___x_7755_ = leanh::lean_box((v_skipConstInApp_7731_) as usize);
        v___x_7756_ = leanh::lean_box((v_skipInstances_7724_) as usize);
        leanh::lean_inc_n(v___y_7740_, 2);
        leanh::lean_inc(v_x_7733_);
        leanh::lean_inc(v_post_7729_);
        leanh::lean_inc(v_pre_7728_);
        leanh::lean_inc_ref(v_inst_7727_);
        leanh::lean_inc_n(v_inst_7726_, 2);
        leanh::lean_inc_ref(v_inst_7725_);
        leanh::lean_inc_ref(v_f_7739_);
        v___f_7757_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed as *mut core::ffi::c_void, 13, 12);
        leanh::lean_closure_set(v___f_7757_, 0, v_f_7739_);
        leanh::lean_closure_set(v___f_7757_, 1, v_inst_7725_);
        leanh::lean_closure_set(v___f_7757_, 2, v_inst_7726_);
        leanh::lean_closure_set(v___f_7757_, 3, v_inst_7727_);
        leanh::lean_closure_set(v___f_7757_, 4, v_pre_7728_);
        leanh::lean_closure_set(v___f_7757_, 5, v_post_7729_);
        leanh::lean_closure_set(v___f_7757_, 6, v___x_7754_);
        leanh::lean_closure_set(v___f_7757_, 7, v___x_7755_);
        leanh::lean_closure_set(v___f_7757_, 8, v___x_7756_);
        leanh::lean_closure_set(v___f_7757_, 9, v_x_7732_);
        leanh::lean_closure_set(v___f_7757_, 10, v_x_7733_);
        leanh::lean_closure_set(v___f_7757_, 11, v___y_7740_);
        v___x_7758_ = lean_array_get_size(v_args_7734_);
        v___x_7759_ = leanh::lean_box((v_usedLetOnly_7730_) as usize);
        v___x_7760_ = leanh::lean_box((v_skipConstInApp_7731_) as usize);
        v___x_7761_ = leanh::lean_box((v_skipInstances_7724_) as usize);
        leanh::lean_inc(v_toBind_7736_);
        v___f_7762_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed as *mut core::ffi::c_void, 18, 17);
        leanh::lean_closure_set(v___f_7762_, 0, v___x_7758_);
        leanh::lean_closure_set(v___f_7762_, 1, v_toApplicative_7737_);
        leanh::lean_closure_set(v___f_7762_, 2, v_toBind_7736_);
        leanh::lean_closure_set(v___f_7762_, 3, v___f_7738_);
        leanh::lean_closure_set(v___f_7762_, 4, v_inst_7725_);
        leanh::lean_closure_set(v___f_7762_, 5, v_inst_7726_);
        leanh::lean_closure_set(v___f_7762_, 6, v_inst_7727_);
        leanh::lean_closure_set(v___f_7762_, 7, v_pre_7728_);
        leanh::lean_closure_set(v___f_7762_, 8, v_post_7729_);
        leanh::lean_closure_set(v___f_7762_, 9, v___x_7759_);
        leanh::lean_closure_set(v___f_7762_, 10, v___x_7760_);
        leanh::lean_closure_set(v___f_7762_, 11, v___x_7761_);
        leanh::lean_closure_set(v___f_7762_, 12, v_x_7732_);
        leanh::lean_closure_set(v___f_7762_, 13, v_x_7733_);
        leanh::lean_closure_set(v___f_7762_, 14, v_args_7734_);
        leanh::lean_closure_set(v___f_7762_, 15, v___y_7740_);
        leanh::lean_closure_set(v___f_7762_, 16, v___f_7757_);
        v___x_7763_ = leanh::lean_alloc_closure(
            l_Lean_Meta_getFunInfoNArgs___boxed as *mut core::ffi::c_void,
            7,
            2,
        );
        leanh::lean_closure_set(v___x_7763_, 0, v_f_7739_);
        leanh::lean_closure_set(v___x_7763_, 1, v___x_7758_);
        v___x_7764_ =
            leanh::lean_apply_2(v_inst_7726_, leanh::lean_box(0), v___x_7763_);
        v___x_7765_ = leanh::lean_apply_4(
            v_toBind_7736_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_7764_,
            v___f_7762_,
        );
        return v___x_7765_;
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipInstances_7766_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_inst_7767_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_inst_7768_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_inst_7769_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_pre_7770_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_post_7771_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_usedLetOnly_7772_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_skipConstInApp_7773_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_x_7774_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_x_7775_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_args_7776_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___x_7777_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_toBind_7778_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_toApplicative_7779_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___f_7780_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_f_7781_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_7782_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_skipInstances_boxed_7783_: u8 = 0;
    let mut v_usedLetOnly_boxed_7784_: u8 = 0;
    let mut v_skipConstInApp_boxed_7785_: u8 = 0;
    let mut v_res_7786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_skipInstances_boxed_7783_ = (leanh::lean_unbox(v_skipInstances_7766_) as u8);
    v_usedLetOnly_boxed_7784_ = (leanh::lean_unbox(v_usedLetOnly_7772_) as u8);
    v_skipConstInApp_boxed_7785_ = (leanh::lean_unbox(v_skipConstInApp_7773_) as u8);
    v_res_7786_ =
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(
            v_skipInstances_boxed_7783_,
            v_inst_7767_,
            v_inst_7768_,
            v_inst_7769_,
            v_pre_7770_,
            v_post_7771_,
            v_usedLetOnly_boxed_7784_,
            v_skipConstInApp_boxed_7785_,
            v_x_7774_,
            v_x_7775_,
            v_args_7776_,
            v___x_7777_,
            v_toBind_7778_,
            v_toApplicative_7779_,
            v___f_7780_,
            v_f_7781_,
            v___y_7782_,
        );
    leanh::lean_dec(v___y_7782_);
    return v_res_7786_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(
    mut v_skipInstances_7787_: u8,
    mut v_inst_7788_: *mut leanh::LeanObject,
    mut v_inst_7789_: *mut leanh::LeanObject,
    mut v_inst_7790_: *mut leanh::LeanObject,
    mut v_pre_7791_: *mut leanh::LeanObject,
    mut v_post_7792_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7793_: u8,
    mut v_skipConstInApp_7794_: u8,
    mut v_x_7795_: *mut leanh::LeanObject,
    mut v_x_7796_: *mut leanh::LeanObject,
    mut v___x_7797_: *mut leanh::LeanObject,
    mut v_toBind_7798_: *mut leanh::LeanObject,
    mut v_toApplicative_7799_: *mut leanh::LeanObject,
    mut v___f_7800_: *mut leanh::LeanObject,
    mut v_f_7801_: *mut leanh::LeanObject,
    mut v_args_7802_: *mut leanh::LeanObject,
    mut v___y_7803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7812_: u8 = 0;
    let mut v_toPure_7813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7804_ = leanh::lean_box((v_skipInstances_7787_) as usize);
                v___x_7805_ = leanh::lean_box((v_usedLetOnly_7793_) as usize);
                v___x_7806_ = leanh::lean_box((v_skipConstInApp_7794_) as usize);
                leanh::lean_inc_ref(v_toApplicative_7799_);
                leanh::lean_inc(v_toBind_7798_);
                leanh::lean_inc(v_x_7796_);
                leanh::lean_inc(v_post_7792_);
                leanh::lean_inc(v_pre_7791_);
                leanh::lean_inc_ref(v_inst_7790_);
                leanh::lean_inc(v_inst_7789_);
                leanh::lean_inc_ref(v_inst_7788_);
                v___f_7807_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed as *mut core::ffi::c_void, 17, 15);
                leanh::lean_closure_set(v___f_7807_, 0, v___x_7804_);
                leanh::lean_closure_set(v___f_7807_, 1, v_inst_7788_);
                leanh::lean_closure_set(v___f_7807_, 2, v_inst_7789_);
                leanh::lean_closure_set(v___f_7807_, 3, v_inst_7790_);
                leanh::lean_closure_set(v___f_7807_, 4, v_pre_7791_);
                leanh::lean_closure_set(v___f_7807_, 5, v_post_7792_);
                leanh::lean_closure_set(v___f_7807_, 6, v___x_7805_);
                leanh::lean_closure_set(v___f_7807_, 7, v___x_7806_);
                leanh::lean_closure_set(v___f_7807_, 8, v_x_7795_);
                leanh::lean_closure_set(v___f_7807_, 9, v_x_7796_);
                leanh::lean_closure_set(v___f_7807_, 10, v_args_7802_);
                leanh::lean_closure_set(v___f_7807_, 11, v___x_7797_);
                leanh::lean_closure_set(v___f_7807_, 12, v_toBind_7798_);
                leanh::lean_closure_set(v___f_7807_, 13, v_toApplicative_7799_);
                leanh::lean_closure_set(v___f_7807_, 14, v___f_7800_);
                leanh::lean_inc(v___y_7803_);
                v___f_7808_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed as *mut core::ffi::c_void, 3, 2);
                leanh::lean_closure_set(v___f_7808_, 0, v___f_7807_);
                leanh::lean_closure_set(v___f_7808_, 1, v___y_7803_);
                if v_skipConstInApp_7794_ == 0 {
                    leanh::lean_dec_ref(v_toApplicative_7799_);
                    state = 1;
                    continue;
                } else {
                    v___x_7812_ = l_Lean_Expr_isConst(v_f_7801_);
                    if v___x_7812_ == 0 {
                        leanh::lean_dec_ref(v_toApplicative_7799_);
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_7796_);
                        leanh::lean_dec(v_post_7792_);
                        leanh::lean_dec(v_pre_7791_);
                        leanh::lean_dec_ref(v_inst_7790_);
                        leanh::lean_dec(v_inst_7789_);
                        leanh::lean_dec_ref(v_inst_7788_);
                        v_toPure_7813_ = leanh::lean_ctor_get(v_toApplicative_7799_, 1);
                        leanh::lean_inc(v_toPure_7813_);
                        leanh::lean_dec_ref(v_toApplicative_7799_);
                        v___x_7814_ = leanh::lean_apply_2(
                            v_toPure_7813_,
                            leanh::lean_box(0),
                            v_f_7801_,
                        );
                        v___x_7815_ = leanh::lean_apply_4(
                            v_toBind_7798_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_7814_,
                            v___f_7808_,
                        );
                        return v___x_7815_;
                    }
                }
            }
            1 => {
                v___x_7810_ =
                    l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(
                        v_inst_7788_,
                        v_inst_7789_,
                        v_inst_7790_,
                        v_pre_7791_,
                        v_post_7792_,
                        v_usedLetOnly_7793_,
                        v_skipConstInApp_7794_,
                        v_skipInstances_7787_,
                        v_x_7795_,
                        v_x_7796_,
                        v_f_7801_,
                        v___y_7803_,
                    );
                v___x_7811_ = leanh::lean_apply_4(
                    v_toBind_7798_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_7810_,
                    v___f_7808_,
                );
                return v___x_7811_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipInstances_7816_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_inst_7817_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_inst_7818_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_inst_7819_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_pre_7820_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_post_7821_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_usedLetOnly_7822_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_skipConstInApp_7823_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_x_7824_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_x_7825_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___x_7826_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_toBind_7827_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_toApplicative_7828_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___f_7829_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_f_7830_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_args_7831_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_7832_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_skipInstances_boxed_7833_: u8 = 0;
    let mut v_usedLetOnly_boxed_7834_: u8 = 0;
    let mut v_skipConstInApp_boxed_7835_: u8 = 0;
    let mut v_res_7836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_skipInstances_boxed_7833_ = (leanh::lean_unbox(v_skipInstances_7816_) as u8);
    v_usedLetOnly_boxed_7834_ = (leanh::lean_unbox(v_usedLetOnly_7822_) as u8);
    v_skipConstInApp_boxed_7835_ = (leanh::lean_unbox(v_skipConstInApp_7823_) as u8);
    v_res_7836_ =
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(
            v_skipInstances_boxed_7833_,
            v_inst_7817_,
            v_inst_7818_,
            v_inst_7819_,
            v_pre_7820_,
            v_post_7821_,
            v_usedLetOnly_boxed_7834_,
            v_skipConstInApp_boxed_7835_,
            v_x_7824_,
            v_x_7825_,
            v___x_7826_,
            v_toBind_7827_,
            v_toApplicative_7828_,
            v___f_7829_,
            v_f_7830_,
            v_args_7831_,
            v___y_7832_,
        );
    leanh::lean_dec(v___y_7832_);
    return v_res_7836_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(
    mut v_fvars_7839_: *mut leanh::LeanObject,
    mut v_inst_7840_: *mut leanh::LeanObject,
    mut v_inst_7841_: *mut leanh::LeanObject,
    mut v_inst_7842_: *mut leanh::LeanObject,
    mut v_pre_7843_: *mut leanh::LeanObject,
    mut v_post_7844_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7845_: u8,
    mut v_skipConstInApp_7846_: u8,
    mut v_skipInstances_7847_: u8,
    mut v_x_7848_: *mut leanh::LeanObject,
    mut v_x_7849_: *mut leanh::LeanObject,
    mut v_body_7850_: *mut leanh::LeanObject,
    mut v_x_7851_: *mut leanh::LeanObject,
    mut v___y_7852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7853_ = lean_array_push(v_fvars_7839_, v_x_7851_);
    v___x_7854_ =
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(
            v_inst_7840_,
            v_inst_7841_,
            v_inst_7842_,
            v_pre_7843_,
            v_post_7844_,
            v_usedLetOnly_7845_,
            v_skipConstInApp_7846_,
            v_skipInstances_7847_,
            v_x_7848_,
            v_x_7849_,
            v___x_7853_,
            v_body_7850_,
            v___y_7852_,
        );
    return v___x_7854_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed(
    mut v_fvars_7855_: *mut leanh::LeanObject,
    mut v_inst_7856_: *mut leanh::LeanObject,
    mut v_inst_7857_: *mut leanh::LeanObject,
    mut v_inst_7858_: *mut leanh::LeanObject,
    mut v_pre_7859_: *mut leanh::LeanObject,
    mut v_post_7860_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7861_: *mut leanh::LeanObject,
    mut v_skipConstInApp_7862_: *mut leanh::LeanObject,
    mut v_skipInstances_7863_: *mut leanh::LeanObject,
    mut v_x_7864_: *mut leanh::LeanObject,
    mut v_x_7865_: *mut leanh::LeanObject,
    mut v_body_7866_: *mut leanh::LeanObject,
    mut v_x_7867_: *mut leanh::LeanObject,
    mut v___y_7868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7869_: u8 = 0;
    let mut v_skipConstInApp_boxed_7870_: u8 = 0;
    let mut v_skipInstances_boxed_7871_: u8 = 0;
    let mut v_res_7872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7869_ = (leanh::lean_unbox(v_usedLetOnly_7861_) as u8);
    v_skipConstInApp_boxed_7870_ = (leanh::lean_unbox(v_skipConstInApp_7862_) as u8);
    v_skipInstances_boxed_7871_ = (leanh::lean_unbox(v_skipInstances_7863_) as u8);
    v_res_7872_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(v_fvars_7855_, v_inst_7856_, v_inst_7857_, v_inst_7858_, v_pre_7859_, v_post_7860_, v_usedLetOnly_boxed_7869_, v_skipConstInApp_boxed_7870_, v_skipInstances_boxed_7871_, v_x_7864_, v_x_7865_, v_body_7866_, v_x_7867_, v___y_7868_);
    leanh::lean_dec(v___y_7868_);
    return v_res_7872_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed(
    mut v_inst_7873_: *mut leanh::LeanObject,
    mut v_inst_7874_: *mut leanh::LeanObject,
    mut v_inst_7875_: *mut leanh::LeanObject,
    mut v_pre_7876_: *mut leanh::LeanObject,
    mut v_post_7877_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7878_: *mut leanh::LeanObject,
    mut v_skipConstInApp_7879_: *mut leanh::LeanObject,
    mut v_skipInstances_7880_: *mut leanh::LeanObject,
    mut v_x_7881_: *mut leanh::LeanObject,
    mut v_x_7882_: *mut leanh::LeanObject,
    mut v_a_7883_: *mut leanh::LeanObject,
    mut v_a_7884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7885_: u8 = 0;
    let mut v_skipConstInApp_boxed_7886_: u8 = 0;
    let mut v_skipInstances_boxed_7887_: u8 = 0;
    let mut v_res_7888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7885_ = (leanh::lean_unbox(v_usedLetOnly_7878_) as u8);
    v_skipConstInApp_boxed_7886_ = (leanh::lean_unbox(v_skipConstInApp_7879_) as u8);
    v_skipInstances_boxed_7887_ = (leanh::lean_unbox(v_skipInstances_7880_) as u8);
    v_res_7888_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(v_inst_7873_, v_inst_7874_, v_inst_7875_, v_pre_7876_, v_post_7877_, v_usedLetOnly_boxed_7885_, v_skipConstInApp_boxed_7886_, v_skipInstances_boxed_7887_, v_x_7881_, v_x_7882_, v_a_7883_, v_a_7884_);
    leanh::lean_dec(v_a_7883_);
    return v_res_7888_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(
    mut v_inst_7889_: *mut leanh::LeanObject,
    mut v_inst_7890_: *mut leanh::LeanObject,
    mut v_inst_7891_: *mut leanh::LeanObject,
    mut v_pre_7892_: *mut leanh::LeanObject,
    mut v_post_7893_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7894_: u8,
    mut v_skipConstInApp_7895_: u8,
    mut v_skipInstances_7896_: u8,
    mut v_x_7897_: *mut leanh::LeanObject,
    mut v_x_7898_: *mut leanh::LeanObject,
    mut v_fvars_7899_: *mut leanh::LeanObject,
    mut v_e_7900_: *mut leanh::LeanObject,
    mut v_a_7901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7902_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0;
    v___x_7903_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1;
    leanh::lean_inc_ref(v_inst_7889_);
    v___x_7904_ =
        l_Lean_MonadCacheT_instMonad___redArg(v_x_7897_, v___x_7902_, v___x_7903_, v_inst_7889_);
    v___x_7905_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_7897_, v___x_7902_, v___x_7903_);
    leanh::lean_inc_ref_n(v_inst_7891_, 2);
    leanh::lean_inc_ref(v___x_7905_);
    v___f_7906_ = leanh::lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__3 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_7906_, 0, v___x_7905_);
    leanh::lean_closure_set(v___f_7906_, 1, v_inst_7891_);
    v___f_7907_ = leanh::lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__4 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_7907_, 0, v___x_7905_);
    leanh::lean_closure_set(v___f_7907_, 1, v_inst_7891_);
    v___x_7908_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7908_, 0, v___f_7906_);
    leanh::lean_ctor_set(v___x_7908_, 1, v___f_7907_);
    if leanh::lean_obj_tag(v_e_7900_) == 7 {
        let mut v_binderName_7909_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_7910_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_7911_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_7912_: u8 = 0;
        let mut v_toBind_7913_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7914_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7915_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7916_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_7917_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7918_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_7919_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7920_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7921_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7922_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_binderName_7909_ = leanh::lean_ctor_get(v_e_7900_, 0);
        leanh::lean_inc(v_binderName_7909_);
        v_binderType_7910_ = leanh::lean_ctor_get(v_e_7900_, 1);
        leanh::lean_inc_ref(v_binderType_7910_);
        v_body_7911_ = leanh::lean_ctor_get(v_e_7900_, 2);
        leanh::lean_inc_ref(v_body_7911_);
        v_binderInfo_7912_ = leanh::lean_ctor_get_uint8(
            v_e_7900_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
        );
        leanh::lean_dec_ref_known(v_e_7900_, 3);
        v_toBind_7913_ = leanh::lean_ctor_get(v_inst_7889_, 1);
        leanh::lean_inc(v_toBind_7913_);
        v___x_7914_ = leanh::lean_box((v_usedLetOnly_7894_) as usize);
        v___x_7915_ = leanh::lean_box((v_skipConstInApp_7895_) as usize);
        v___x_7916_ = leanh::lean_box((v_skipInstances_7896_) as usize);
        leanh::lean_inc(v_x_7898_);
        leanh::lean_inc(v_post_7893_);
        leanh::lean_inc(v_pre_7892_);
        leanh::lean_inc_ref(v_inst_7891_);
        leanh::lean_inc(v_inst_7890_);
        leanh::lean_inc_ref(v_inst_7889_);
        leanh::lean_inc_ref(v_fvars_7899_);
        v___f_7917_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 12);
        leanh::lean_closure_set(v___f_7917_, 0, v_fvars_7899_);
        leanh::lean_closure_set(v___f_7917_, 1, v_inst_7889_);
        leanh::lean_closure_set(v___f_7917_, 2, v_inst_7890_);
        leanh::lean_closure_set(v___f_7917_, 3, v_inst_7891_);
        leanh::lean_closure_set(v___f_7917_, 4, v_pre_7892_);
        leanh::lean_closure_set(v___f_7917_, 5, v_post_7893_);
        leanh::lean_closure_set(v___f_7917_, 6, v___x_7914_);
        leanh::lean_closure_set(v___f_7917_, 7, v___x_7915_);
        leanh::lean_closure_set(v___f_7917_, 8, v___x_7916_);
        leanh::lean_closure_set(v___f_7917_, 9, v_x_7897_);
        leanh::lean_closure_set(v___f_7917_, 10, v_x_7898_);
        leanh::lean_closure_set(v___f_7917_, 11, v_body_7911_);
        v___x_7918_ = leanh::lean_box((v_binderInfo_7912_) as usize);
        leanh::lean_inc(v_a_7901_);
        v___f_7919_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed as *mut core::ffi::c_void, 7, 6);
        leanh::lean_closure_set(v___f_7919_, 0, v___x_7908_);
        leanh::lean_closure_set(v___f_7919_, 1, v___x_7904_);
        leanh::lean_closure_set(v___f_7919_, 2, v_binderName_7909_);
        leanh::lean_closure_set(v___f_7919_, 3, v___x_7918_);
        leanh::lean_closure_set(v___f_7919_, 4, v___f_7917_);
        leanh::lean_closure_set(v___f_7919_, 5, v_a_7901_);
        v___x_7920_ = lean_expr_instantiate_rev(v_binderType_7910_, v_fvars_7899_);
        leanh::lean_dec_ref(v_fvars_7899_);
        leanh::lean_dec_ref(v_binderType_7910_);
        v___x_7921_ =
            l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(
                v_inst_7889_,
                v_inst_7890_,
                v_inst_7891_,
                v_pre_7892_,
                v_post_7893_,
                v_usedLetOnly_7894_,
                v_skipConstInApp_7895_,
                v_skipInstances_7896_,
                v_x_7897_,
                v_x_7898_,
                v___x_7920_,
                v_a_7901_,
            );
        v___x_7922_ = leanh::lean_apply_4(
            v_toBind_7913_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_7921_,
            v___f_7919_,
        );
        return v___x_7922_;
    } else {
        let mut v_toBind_7923_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7924_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7925_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7926_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_7927_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7928_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_7929_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7930_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7931_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7932_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_7908_, 2);
        leanh::lean_dec_ref(v___x_7904_);
        v_toBind_7923_ = leanh::lean_ctor_get(v_inst_7889_, 1);
        leanh::lean_inc_n(v_toBind_7923_, 2);
        v___x_7924_ = leanh::lean_box((v_usedLetOnly_7894_) as usize);
        v___x_7925_ = leanh::lean_box((v_skipConstInApp_7895_) as usize);
        v___x_7926_ = leanh::lean_box((v_skipInstances_7896_) as usize);
        leanh::lean_inc(v_a_7901_);
        leanh::lean_inc(v_x_7898_);
        leanh::lean_inc(v_post_7893_);
        leanh::lean_inc(v_pre_7892_);
        leanh::lean_inc_ref(v_inst_7891_);
        leanh::lean_inc_n(v_inst_7890_, 2);
        leanh::lean_inc_ref(v_inst_7889_);
        v___f_7927_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed as *mut core::ffi::c_void, 12, 11);
        leanh::lean_closure_set(v___f_7927_, 0, v_inst_7889_);
        leanh::lean_closure_set(v___f_7927_, 1, v_inst_7890_);
        leanh::lean_closure_set(v___f_7927_, 2, v_inst_7891_);
        leanh::lean_closure_set(v___f_7927_, 3, v_pre_7892_);
        leanh::lean_closure_set(v___f_7927_, 4, v_post_7893_);
        leanh::lean_closure_set(v___f_7927_, 5, v___x_7924_);
        leanh::lean_closure_set(v___f_7927_, 6, v___x_7925_);
        leanh::lean_closure_set(v___f_7927_, 7, v___x_7926_);
        leanh::lean_closure_set(v___f_7927_, 8, v_x_7897_);
        leanh::lean_closure_set(v___f_7927_, 9, v_x_7898_);
        leanh::lean_closure_set(v___f_7927_, 10, v_a_7901_);
        v___x_7928_ = leanh::lean_box((v_usedLetOnly_7894_) as usize);
        leanh::lean_inc_ref(v_fvars_7899_);
        v___f_7929_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed as *mut core::ffi::c_void, 6, 5);
        leanh::lean_closure_set(v___f_7929_, 0, v_fvars_7899_);
        leanh::lean_closure_set(v___f_7929_, 1, v___x_7928_);
        leanh::lean_closure_set(v___f_7929_, 2, v_inst_7890_);
        leanh::lean_closure_set(v___f_7929_, 3, v_toBind_7923_);
        leanh::lean_closure_set(v___f_7929_, 4, v___f_7927_);
        v___x_7930_ = lean_expr_instantiate_rev(v_e_7900_, v_fvars_7899_);
        leanh::lean_dec_ref(v_fvars_7899_);
        leanh::lean_dec_ref(v_e_7900_);
        v___x_7931_ =
            l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(
                v_inst_7889_,
                v_inst_7890_,
                v_inst_7891_,
                v_pre_7892_,
                v_post_7893_,
                v_usedLetOnly_7894_,
                v_skipConstInApp_7895_,
                v_skipInstances_7896_,
                v_x_7897_,
                v_x_7898_,
                v___x_7930_,
                v_a_7901_,
            );
        v___x_7932_ = leanh::lean_apply_4(
            v_toBind_7923_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_7931_,
            v___f_7929_,
        );
        return v___x_7932_;
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(
    mut v_fvars_7933_: *mut leanh::LeanObject,
    mut v_inst_7934_: *mut leanh::LeanObject,
    mut v_inst_7935_: *mut leanh::LeanObject,
    mut v_inst_7936_: *mut leanh::LeanObject,
    mut v_pre_7937_: *mut leanh::LeanObject,
    mut v_post_7938_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7939_: u8,
    mut v_skipConstInApp_7940_: u8,
    mut v_skipInstances_7941_: u8,
    mut v_x_7942_: *mut leanh::LeanObject,
    mut v_x_7943_: *mut leanh::LeanObject,
    mut v_body_7944_: *mut leanh::LeanObject,
    mut v_x_7945_: *mut leanh::LeanObject,
    mut v___y_7946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7947_ = lean_array_push(v_fvars_7933_, v_x_7945_);
    v___x_7948_ =
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(
            v_inst_7934_,
            v_inst_7935_,
            v_inst_7936_,
            v_pre_7937_,
            v_post_7938_,
            v_usedLetOnly_7939_,
            v_skipConstInApp_7940_,
            v_skipInstances_7941_,
            v_x_7942_,
            v_x_7943_,
            v___x_7947_,
            v_body_7944_,
            v___y_7946_,
        );
    return v___x_7948_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed(
    mut v_fvars_7949_: *mut leanh::LeanObject,
    mut v_inst_7950_: *mut leanh::LeanObject,
    mut v_inst_7951_: *mut leanh::LeanObject,
    mut v_inst_7952_: *mut leanh::LeanObject,
    mut v_pre_7953_: *mut leanh::LeanObject,
    mut v_post_7954_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7955_: *mut leanh::LeanObject,
    mut v_skipConstInApp_7956_: *mut leanh::LeanObject,
    mut v_skipInstances_7957_: *mut leanh::LeanObject,
    mut v_x_7958_: *mut leanh::LeanObject,
    mut v_x_7959_: *mut leanh::LeanObject,
    mut v_body_7960_: *mut leanh::LeanObject,
    mut v_x_7961_: *mut leanh::LeanObject,
    mut v___y_7962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7963_: u8 = 0;
    let mut v_skipConstInApp_boxed_7964_: u8 = 0;
    let mut v_skipInstances_boxed_7965_: u8 = 0;
    let mut v_res_7966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7963_ = (leanh::lean_unbox(v_usedLetOnly_7955_) as u8);
    v_skipConstInApp_boxed_7964_ = (leanh::lean_unbox(v_skipConstInApp_7956_) as u8);
    v_skipInstances_boxed_7965_ = (leanh::lean_unbox(v_skipInstances_7957_) as u8);
    v_res_7966_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(v_fvars_7949_, v_inst_7950_, v_inst_7951_, v_inst_7952_, v_pre_7953_, v_post_7954_, v_usedLetOnly_boxed_7963_, v_skipConstInApp_boxed_7964_, v_skipInstances_boxed_7965_, v_x_7958_, v_x_7959_, v_body_7960_, v_x_7961_, v___y_7962_);
    leanh::lean_dec(v___y_7962_);
    return v_res_7966_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(
    mut v_inst_7967_: *mut leanh::LeanObject,
    mut v_inst_7968_: *mut leanh::LeanObject,
    mut v_inst_7969_: *mut leanh::LeanObject,
    mut v_pre_7970_: *mut leanh::LeanObject,
    mut v_post_7971_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7972_: u8,
    mut v_skipConstInApp_7973_: u8,
    mut v_skipInstances_7974_: u8,
    mut v_x_7975_: *mut leanh::LeanObject,
    mut v_x_7976_: *mut leanh::LeanObject,
    mut v_fvars_7977_: *mut leanh::LeanObject,
    mut v_e_7978_: *mut leanh::LeanObject,
    mut v_a_7979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7980_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0;
    v___x_7981_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1;
    leanh::lean_inc_ref(v_inst_7967_);
    v___x_7982_ =
        l_Lean_MonadCacheT_instMonad___redArg(v_x_7975_, v___x_7980_, v___x_7981_, v_inst_7967_);
    v___x_7983_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_7975_, v___x_7980_, v___x_7981_);
    leanh::lean_inc_ref_n(v_inst_7969_, 2);
    leanh::lean_inc_ref(v___x_7983_);
    v___f_7984_ = leanh::lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__3 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_7984_, 0, v___x_7983_);
    leanh::lean_closure_set(v___f_7984_, 1, v_inst_7969_);
    v___f_7985_ = leanh::lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__4 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_7985_, 0, v___x_7983_);
    leanh::lean_closure_set(v___f_7985_, 1, v_inst_7969_);
    v___x_7986_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7986_, 0, v___f_7984_);
    leanh::lean_ctor_set(v___x_7986_, 1, v___f_7985_);
    if leanh::lean_obj_tag(v_e_7978_) == 6 {
        let mut v_binderName_7987_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_7988_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_7989_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_7990_: u8 = 0;
        let mut v_toBind_7991_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7992_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7993_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7994_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_7995_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7996_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_7997_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7998_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7999_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8000_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_binderName_7987_ = leanh::lean_ctor_get(v_e_7978_, 0);
        leanh::lean_inc(v_binderName_7987_);
        v_binderType_7988_ = leanh::lean_ctor_get(v_e_7978_, 1);
        leanh::lean_inc_ref(v_binderType_7988_);
        v_body_7989_ = leanh::lean_ctor_get(v_e_7978_, 2);
        leanh::lean_inc_ref(v_body_7989_);
        v_binderInfo_7990_ = leanh::lean_ctor_get_uint8(
            v_e_7978_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
        );
        leanh::lean_dec_ref_known(v_e_7978_, 3);
        v_toBind_7991_ = leanh::lean_ctor_get(v_inst_7967_, 1);
        leanh::lean_inc(v_toBind_7991_);
        v___x_7992_ = leanh::lean_box((v_usedLetOnly_7972_) as usize);
        v___x_7993_ = leanh::lean_box((v_skipConstInApp_7973_) as usize);
        v___x_7994_ = leanh::lean_box((v_skipInstances_7974_) as usize);
        leanh::lean_inc(v_x_7976_);
        leanh::lean_inc(v_post_7971_);
        leanh::lean_inc(v_pre_7970_);
        leanh::lean_inc_ref(v_inst_7969_);
        leanh::lean_inc(v_inst_7968_);
        leanh::lean_inc_ref(v_inst_7967_);
        leanh::lean_inc_ref(v_fvars_7977_);
        v___f_7995_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 12);
        leanh::lean_closure_set(v___f_7995_, 0, v_fvars_7977_);
        leanh::lean_closure_set(v___f_7995_, 1, v_inst_7967_);
        leanh::lean_closure_set(v___f_7995_, 2, v_inst_7968_);
        leanh::lean_closure_set(v___f_7995_, 3, v_inst_7969_);
        leanh::lean_closure_set(v___f_7995_, 4, v_pre_7970_);
        leanh::lean_closure_set(v___f_7995_, 5, v_post_7971_);
        leanh::lean_closure_set(v___f_7995_, 6, v___x_7992_);
        leanh::lean_closure_set(v___f_7995_, 7, v___x_7993_);
        leanh::lean_closure_set(v___f_7995_, 8, v___x_7994_);
        leanh::lean_closure_set(v___f_7995_, 9, v_x_7975_);
        leanh::lean_closure_set(v___f_7995_, 10, v_x_7976_);
        leanh::lean_closure_set(v___f_7995_, 11, v_body_7989_);
        v___x_7996_ = leanh::lean_box((v_binderInfo_7990_) as usize);
        leanh::lean_inc(v_a_7979_);
        v___f_7997_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed as *mut core::ffi::c_void, 7, 6);
        leanh::lean_closure_set(v___f_7997_, 0, v___x_7986_);
        leanh::lean_closure_set(v___f_7997_, 1, v___x_7982_);
        leanh::lean_closure_set(v___f_7997_, 2, v_binderName_7987_);
        leanh::lean_closure_set(v___f_7997_, 3, v___x_7996_);
        leanh::lean_closure_set(v___f_7997_, 4, v___f_7995_);
        leanh::lean_closure_set(v___f_7997_, 5, v_a_7979_);
        v___x_7998_ = lean_expr_instantiate_rev(v_binderType_7988_, v_fvars_7977_);
        leanh::lean_dec_ref(v_fvars_7977_);
        leanh::lean_dec_ref(v_binderType_7988_);
        v___x_7999_ =
            l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(
                v_inst_7967_,
                v_inst_7968_,
                v_inst_7969_,
                v_pre_7970_,
                v_post_7971_,
                v_usedLetOnly_7972_,
                v_skipConstInApp_7973_,
                v_skipInstances_7974_,
                v_x_7975_,
                v_x_7976_,
                v___x_7998_,
                v_a_7979_,
            );
        v___x_8000_ = leanh::lean_apply_4(
            v_toBind_7991_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_7999_,
            v___f_7997_,
        );
        return v___x_8000_;
    } else {
        let mut v_toBind_8001_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8002_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8003_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8004_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_8005_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8006_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_8007_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8008_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8009_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8010_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_7986_, 2);
        leanh::lean_dec_ref(v___x_7982_);
        v_toBind_8001_ = leanh::lean_ctor_get(v_inst_7967_, 1);
        leanh::lean_inc_n(v_toBind_8001_, 2);
        v___x_8002_ = leanh::lean_box((v_usedLetOnly_7972_) as usize);
        v___x_8003_ = leanh::lean_box((v_skipConstInApp_7973_) as usize);
        v___x_8004_ = leanh::lean_box((v_skipInstances_7974_) as usize);
        leanh::lean_inc(v_a_7979_);
        leanh::lean_inc(v_x_7976_);
        leanh::lean_inc(v_post_7971_);
        leanh::lean_inc(v_pre_7970_);
        leanh::lean_inc_ref(v_inst_7969_);
        leanh::lean_inc_n(v_inst_7968_, 2);
        leanh::lean_inc_ref(v_inst_7967_);
        v___f_8005_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed as *mut core::ffi::c_void, 12, 11);
        leanh::lean_closure_set(v___f_8005_, 0, v_inst_7967_);
        leanh::lean_closure_set(v___f_8005_, 1, v_inst_7968_);
        leanh::lean_closure_set(v___f_8005_, 2, v_inst_7969_);
        leanh::lean_closure_set(v___f_8005_, 3, v_pre_7970_);
        leanh::lean_closure_set(v___f_8005_, 4, v_post_7971_);
        leanh::lean_closure_set(v___f_8005_, 5, v___x_8002_);
        leanh::lean_closure_set(v___f_8005_, 6, v___x_8003_);
        leanh::lean_closure_set(v___f_8005_, 7, v___x_8004_);
        leanh::lean_closure_set(v___f_8005_, 8, v_x_7975_);
        leanh::lean_closure_set(v___f_8005_, 9, v_x_7976_);
        leanh::lean_closure_set(v___f_8005_, 10, v_a_7979_);
        v___x_8006_ = leanh::lean_box((v_usedLetOnly_7972_) as usize);
        leanh::lean_inc_ref(v_fvars_7977_);
        v___f_8007_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed as *mut core::ffi::c_void, 6, 5);
        leanh::lean_closure_set(v___f_8007_, 0, v_fvars_7977_);
        leanh::lean_closure_set(v___f_8007_, 1, v___x_8006_);
        leanh::lean_closure_set(v___f_8007_, 2, v_inst_7968_);
        leanh::lean_closure_set(v___f_8007_, 3, v_toBind_8001_);
        leanh::lean_closure_set(v___f_8007_, 4, v___f_8005_);
        v___x_8008_ = lean_expr_instantiate_rev(v_e_7978_, v_fvars_7977_);
        leanh::lean_dec_ref(v_fvars_7977_);
        leanh::lean_dec_ref(v_e_7978_);
        v___x_8009_ =
            l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(
                v_inst_7967_,
                v_inst_7968_,
                v_inst_7969_,
                v_pre_7970_,
                v_post_7971_,
                v_usedLetOnly_7972_,
                v_skipConstInApp_7973_,
                v_skipInstances_7974_,
                v_x_7975_,
                v_x_7976_,
                v___x_8008_,
                v_a_7979_,
            );
        v___x_8010_ = leanh::lean_apply_4(
            v_toBind_8001_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_8009_,
            v___f_8007_,
        );
        return v___x_8010_;
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(
    mut v_fvars_8011_: *mut leanh::LeanObject,
    mut v_inst_8012_: *mut leanh::LeanObject,
    mut v_inst_8013_: *mut leanh::LeanObject,
    mut v_inst_8014_: *mut leanh::LeanObject,
    mut v_pre_8015_: *mut leanh::LeanObject,
    mut v_post_8016_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8017_: u8,
    mut v_skipConstInApp_8018_: u8,
    mut v_skipInstances_8019_: u8,
    mut v_x_8020_: *mut leanh::LeanObject,
    mut v_x_8021_: *mut leanh::LeanObject,
    mut v_body_8022_: *mut leanh::LeanObject,
    mut v_x_8023_: *mut leanh::LeanObject,
    mut v___y_8024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8025_ = lean_array_push(v_fvars_8011_, v_x_8023_);
    v___x_8026_ =
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(
            v_inst_8012_,
            v_inst_8013_,
            v_inst_8014_,
            v_pre_8015_,
            v_post_8016_,
            v_usedLetOnly_8017_,
            v_skipConstInApp_8018_,
            v_skipInstances_8019_,
            v_x_8020_,
            v_x_8021_,
            v___x_8025_,
            v_body_8022_,
            v___y_8024_,
        );
    return v___x_8026_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed(
    mut v_fvars_8027_: *mut leanh::LeanObject,
    mut v_inst_8028_: *mut leanh::LeanObject,
    mut v_inst_8029_: *mut leanh::LeanObject,
    mut v_inst_8030_: *mut leanh::LeanObject,
    mut v_pre_8031_: *mut leanh::LeanObject,
    mut v_post_8032_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8033_: *mut leanh::LeanObject,
    mut v_skipConstInApp_8034_: *mut leanh::LeanObject,
    mut v_skipInstances_8035_: *mut leanh::LeanObject,
    mut v_x_8036_: *mut leanh::LeanObject,
    mut v_x_8037_: *mut leanh::LeanObject,
    mut v_body_8038_: *mut leanh::LeanObject,
    mut v_x_8039_: *mut leanh::LeanObject,
    mut v___y_8040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_8041_: u8 = 0;
    let mut v_skipConstInApp_boxed_8042_: u8 = 0;
    let mut v_skipInstances_boxed_8043_: u8 = 0;
    let mut v_res_8044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_8041_ = (leanh::lean_unbox(v_usedLetOnly_8033_) as u8);
    v_skipConstInApp_boxed_8042_ = (leanh::lean_unbox(v_skipConstInApp_8034_) as u8);
    v_skipInstances_boxed_8043_ = (leanh::lean_unbox(v_skipInstances_8035_) as u8);
    v_res_8044_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(v_fvars_8027_, v_inst_8028_, v_inst_8029_, v_inst_8030_, v_pre_8031_, v_post_8032_, v_usedLetOnly_boxed_8041_, v_skipConstInApp_boxed_8042_, v_skipInstances_boxed_8043_, v_x_8036_, v_x_8037_, v_body_8038_, v_x_8039_, v___y_8040_);
    leanh::lean_dec(v___y_8040_);
    return v_res_8044_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(
    mut v___x_8045_: *mut leanh::LeanObject,
    mut v___x_8046_: *mut leanh::LeanObject,
    mut v_declName_8047_: *mut leanh::LeanObject,
    mut v___f_8048_: *mut leanh::LeanObject,
    mut v_nondep_8049_: u8,
    mut v_a_8050_: *mut leanh::LeanObject,
    mut v_value_8051_: *mut leanh::LeanObject,
    mut v_fvars_8052_: *mut leanh::LeanObject,
    mut v_inst_8053_: *mut leanh::LeanObject,
    mut v_inst_8054_: *mut leanh::LeanObject,
    mut v_inst_8055_: *mut leanh::LeanObject,
    mut v_pre_8056_: *mut leanh::LeanObject,
    mut v_post_8057_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8058_: u8,
    mut v_skipConstInApp_8059_: u8,
    mut v_skipInstances_8060_: u8,
    mut v_x_8061_: *mut leanh::LeanObject,
    mut v_x_8062_: *mut leanh::LeanObject,
    mut v_toBind_8063_: *mut leanh::LeanObject,
    mut v_a_8064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8065_ = leanh::lean_box((v_nondep_8049_) as usize);
    leanh::lean_inc(v_a_8050_);
    v___f_8066_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed as *mut core::ffi::c_void, 8, 7);
    leanh::lean_closure_set(v___f_8066_, 0, v___x_8045_);
    leanh::lean_closure_set(v___f_8066_, 1, v___x_8046_);
    leanh::lean_closure_set(v___f_8066_, 2, v_declName_8047_);
    leanh::lean_closure_set(v___f_8066_, 3, v_a_8064_);
    leanh::lean_closure_set(v___f_8066_, 4, v___f_8048_);
    leanh::lean_closure_set(v___f_8066_, 5, v___x_8065_);
    leanh::lean_closure_set(v___f_8066_, 6, v_a_8050_);
    v___x_8067_ = lean_expr_instantiate_rev(v_value_8051_, v_fvars_8052_);
    v___x_8068_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(
        v_inst_8053_,
        v_inst_8054_,
        v_inst_8055_,
        v_pre_8056_,
        v_post_8057_,
        v_usedLetOnly_8058_,
        v_skipConstInApp_8059_,
        v_skipInstances_8060_,
        v_x_8061_,
        v_x_8062_,
        v___x_8067_,
        v_a_8050_,
    );
    v___x_8069_ = leanh::lean_apply_4(
        v_toBind_8063_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_8068_,
        v___f_8066_,
    );
    return v___x_8069_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8070_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___x_8071_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_declName_8072_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___f_8073_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_nondep_8074_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_a_8075_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_value_8076_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_fvars_8077_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_inst_8078_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_inst_8079_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_inst_8080_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_pre_8081_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_post_8082_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_usedLetOnly_8083_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_skipConstInApp_8084_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_skipInstances_8085_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_x_8086_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_x_8087_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_toBind_8088_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_a_8089_: *mut leanh::LeanObject = *_args.add(19);
    let mut v_nondep_4209__boxed_8090_: u8 = 0;
    let mut v_usedLetOnly_boxed_8091_: u8 = 0;
    let mut v_skipConstInApp_boxed_8092_: u8 = 0;
    let mut v_skipInstances_boxed_8093_: u8 = 0;
    let mut v_res_8094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_4209__boxed_8090_ = (leanh::lean_unbox(v_nondep_8074_) as u8);
    v_usedLetOnly_boxed_8091_ = (leanh::lean_unbox(v_usedLetOnly_8083_) as u8);
    v_skipConstInApp_boxed_8092_ = (leanh::lean_unbox(v_skipConstInApp_8084_) as u8);
    v_skipInstances_boxed_8093_ = (leanh::lean_unbox(v_skipInstances_8085_) as u8);
    v_res_8094_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(v___x_8070_, v___x_8071_, v_declName_8072_, v___f_8073_, v_nondep_4209__boxed_8090_, v_a_8075_, v_value_8076_, v_fvars_8077_, v_inst_8078_, v_inst_8079_, v_inst_8080_, v_pre_8081_, v_post_8082_, v_usedLetOnly_boxed_8091_, v_skipConstInApp_boxed_8092_, v_skipInstances_boxed_8093_, v_x_8086_, v_x_8087_, v_toBind_8088_, v_a_8089_);
    leanh::lean_dec_ref(v_fvars_8077_);
    leanh::lean_dec_ref(v_value_8076_);
    leanh::lean_dec(v_a_8075_);
    return v_res_8094_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(
    mut v_inst_8095_: *mut leanh::LeanObject,
    mut v_inst_8096_: *mut leanh::LeanObject,
    mut v_inst_8097_: *mut leanh::LeanObject,
    mut v_pre_8098_: *mut leanh::LeanObject,
    mut v_post_8099_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8100_: u8,
    mut v_skipConstInApp_8101_: u8,
    mut v_skipInstances_8102_: u8,
    mut v_x_8103_: *mut leanh::LeanObject,
    mut v_x_8104_: *mut leanh::LeanObject,
    mut v_fvars_8105_: *mut leanh::LeanObject,
    mut v_e_8106_: *mut leanh::LeanObject,
    mut v_a_8107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8108_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0;
    v___x_8109_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1;
    leanh::lean_inc_ref(v_inst_8095_);
    v___x_8110_ =
        l_Lean_MonadCacheT_instMonad___redArg(v_x_8103_, v___x_8108_, v___x_8109_, v_inst_8095_);
    v___x_8111_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_8103_, v___x_8108_, v___x_8109_);
    leanh::lean_inc_ref_n(v_inst_8097_, 2);
    leanh::lean_inc_ref(v___x_8111_);
    v___f_8112_ = leanh::lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__3 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_8112_, 0, v___x_8111_);
    leanh::lean_closure_set(v___f_8112_, 1, v_inst_8097_);
    v___f_8113_ = leanh::lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__4 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_8113_, 0, v___x_8111_);
    leanh::lean_closure_set(v___f_8113_, 1, v_inst_8097_);
    v___x_8114_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_8114_, 0, v___f_8112_);
    leanh::lean_ctor_set(v___x_8114_, 1, v___f_8113_);
    if leanh::lean_obj_tag(v_e_8106_) == 8 {
        let mut v_declName_8115_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_type_8116_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_8117_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_8118_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_nondep_8119_: u8 = 0;
        let mut v_toBind_8120_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8121_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8122_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8123_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_8124_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8125_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8126_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8127_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8128_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_8129_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8130_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8131_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8132_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_declName_8115_ = leanh::lean_ctor_get(v_e_8106_, 0);
        leanh::lean_inc(v_declName_8115_);
        v_type_8116_ = leanh::lean_ctor_get(v_e_8106_, 1);
        leanh::lean_inc_ref(v_type_8116_);
        v_value_8117_ = leanh::lean_ctor_get(v_e_8106_, 2);
        leanh::lean_inc_ref(v_value_8117_);
        v_body_8118_ = leanh::lean_ctor_get(v_e_8106_, 3);
        leanh::lean_inc_ref(v_body_8118_);
        v_nondep_8119_ = leanh::lean_ctor_get_uint8(
            v_e_8106_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8) as u32,
        );
        leanh::lean_dec_ref_known(v_e_8106_, 4);
        v_toBind_8120_ = leanh::lean_ctor_get(v_inst_8095_, 1);
        leanh::lean_inc_n(v_toBind_8120_, 2);
        v___x_8121_ = leanh::lean_box((v_usedLetOnly_8100_) as usize);
        v___x_8122_ = leanh::lean_box((v_skipConstInApp_8101_) as usize);
        v___x_8123_ = leanh::lean_box((v_skipInstances_8102_) as usize);
        leanh::lean_inc_n(v_x_8104_, 2);
        leanh::lean_inc_n(v_post_8099_, 2);
        leanh::lean_inc_n(v_pre_8098_, 2);
        leanh::lean_inc_ref_n(v_inst_8097_, 2);
        leanh::lean_inc_n(v_inst_8096_, 2);
        leanh::lean_inc_ref_n(v_inst_8095_, 2);
        leanh::lean_inc_ref_n(v_fvars_8105_, 2);
        v___f_8124_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 12);
        leanh::lean_closure_set(v___f_8124_, 0, v_fvars_8105_);
        leanh::lean_closure_set(v___f_8124_, 1, v_inst_8095_);
        leanh::lean_closure_set(v___f_8124_, 2, v_inst_8096_);
        leanh::lean_closure_set(v___f_8124_, 3, v_inst_8097_);
        leanh::lean_closure_set(v___f_8124_, 4, v_pre_8098_);
        leanh::lean_closure_set(v___f_8124_, 5, v_post_8099_);
        leanh::lean_closure_set(v___f_8124_, 6, v___x_8121_);
        leanh::lean_closure_set(v___f_8124_, 7, v___x_8122_);
        leanh::lean_closure_set(v___f_8124_, 8, v___x_8123_);
        leanh::lean_closure_set(v___f_8124_, 9, v_x_8103_);
        leanh::lean_closure_set(v___f_8124_, 10, v_x_8104_);
        leanh::lean_closure_set(v___f_8124_, 11, v_body_8118_);
        v___x_8125_ = leanh::lean_box((v_nondep_8119_) as usize);
        v___x_8126_ = leanh::lean_box((v_usedLetOnly_8100_) as usize);
        v___x_8127_ = leanh::lean_box((v_skipConstInApp_8101_) as usize);
        v___x_8128_ = leanh::lean_box((v_skipInstances_8102_) as usize);
        leanh::lean_inc(v_a_8107_);
        v___f_8129_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed as *mut core::ffi::c_void, 20, 19);
        leanh::lean_closure_set(v___f_8129_, 0, v___x_8114_);
        leanh::lean_closure_set(v___f_8129_, 1, v___x_8110_);
        leanh::lean_closure_set(v___f_8129_, 2, v_declName_8115_);
        leanh::lean_closure_set(v___f_8129_, 3, v___f_8124_);
        leanh::lean_closure_set(v___f_8129_, 4, v___x_8125_);
        leanh::lean_closure_set(v___f_8129_, 5, v_a_8107_);
        leanh::lean_closure_set(v___f_8129_, 6, v_value_8117_);
        leanh::lean_closure_set(v___f_8129_, 7, v_fvars_8105_);
        leanh::lean_closure_set(v___f_8129_, 8, v_inst_8095_);
        leanh::lean_closure_set(v___f_8129_, 9, v_inst_8096_);
        leanh::lean_closure_set(v___f_8129_, 10, v_inst_8097_);
        leanh::lean_closure_set(v___f_8129_, 11, v_pre_8098_);
        leanh::lean_closure_set(v___f_8129_, 12, v_post_8099_);
        leanh::lean_closure_set(v___f_8129_, 13, v___x_8126_);
        leanh::lean_closure_set(v___f_8129_, 14, v___x_8127_);
        leanh::lean_closure_set(v___f_8129_, 15, v___x_8128_);
        leanh::lean_closure_set(v___f_8129_, 16, v_x_8103_);
        leanh::lean_closure_set(v___f_8129_, 17, v_x_8104_);
        leanh::lean_closure_set(v___f_8129_, 18, v_toBind_8120_);
        v___x_8130_ = lean_expr_instantiate_rev(v_type_8116_, v_fvars_8105_);
        leanh::lean_dec_ref(v_fvars_8105_);
        leanh::lean_dec_ref(v_type_8116_);
        v___x_8131_ =
            l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(
                v_inst_8095_,
                v_inst_8096_,
                v_inst_8097_,
                v_pre_8098_,
                v_post_8099_,
                v_usedLetOnly_8100_,
                v_skipConstInApp_8101_,
                v_skipInstances_8102_,
                v_x_8103_,
                v_x_8104_,
                v___x_8130_,
                v_a_8107_,
            );
        v___x_8132_ = leanh::lean_apply_4(
            v_toBind_8120_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_8131_,
            v___f_8129_,
        );
        return v___x_8132_;
    } else {
        let mut v_toBind_8133_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8134_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8135_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8136_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_8137_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8138_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_8139_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8140_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8141_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8142_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_8114_, 2);
        leanh::lean_dec_ref(v___x_8110_);
        v_toBind_8133_ = leanh::lean_ctor_get(v_inst_8095_, 1);
        leanh::lean_inc_n(v_toBind_8133_, 2);
        v___x_8134_ = leanh::lean_box((v_usedLetOnly_8100_) as usize);
        v___x_8135_ = leanh::lean_box((v_skipConstInApp_8101_) as usize);
        v___x_8136_ = leanh::lean_box((v_skipInstances_8102_) as usize);
        leanh::lean_inc(v_a_8107_);
        leanh::lean_inc(v_x_8104_);
        leanh::lean_inc(v_post_8099_);
        leanh::lean_inc(v_pre_8098_);
        leanh::lean_inc_ref(v_inst_8097_);
        leanh::lean_inc_n(v_inst_8096_, 2);
        leanh::lean_inc_ref(v_inst_8095_);
        v___f_8137_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed as *mut core::ffi::c_void, 12, 11);
        leanh::lean_closure_set(v___f_8137_, 0, v_inst_8095_);
        leanh::lean_closure_set(v___f_8137_, 1, v_inst_8096_);
        leanh::lean_closure_set(v___f_8137_, 2, v_inst_8097_);
        leanh::lean_closure_set(v___f_8137_, 3, v_pre_8098_);
        leanh::lean_closure_set(v___f_8137_, 4, v_post_8099_);
        leanh::lean_closure_set(v___f_8137_, 5, v___x_8134_);
        leanh::lean_closure_set(v___f_8137_, 6, v___x_8135_);
        leanh::lean_closure_set(v___f_8137_, 7, v___x_8136_);
        leanh::lean_closure_set(v___f_8137_, 8, v_x_8103_);
        leanh::lean_closure_set(v___f_8137_, 9, v_x_8104_);
        leanh::lean_closure_set(v___f_8137_, 10, v_a_8107_);
        v___x_8138_ = leanh::lean_box((v_usedLetOnly_8100_) as usize);
        leanh::lean_inc_ref(v_fvars_8105_);
        v___f_8139_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed as *mut core::ffi::c_void, 6, 5);
        leanh::lean_closure_set(v___f_8139_, 0, v_fvars_8105_);
        leanh::lean_closure_set(v___f_8139_, 1, v___x_8138_);
        leanh::lean_closure_set(v___f_8139_, 2, v_inst_8096_);
        leanh::lean_closure_set(v___f_8139_, 3, v_toBind_8133_);
        leanh::lean_closure_set(v___f_8139_, 4, v___f_8137_);
        v___x_8140_ = lean_expr_instantiate_rev(v_e_8106_, v_fvars_8105_);
        leanh::lean_dec_ref(v_fvars_8105_);
        leanh::lean_dec_ref(v_e_8106_);
        v___x_8141_ =
            l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(
                v_inst_8095_,
                v_inst_8096_,
                v_inst_8097_,
                v_pre_8098_,
                v_post_8099_,
                v_usedLetOnly_8100_,
                v_skipConstInApp_8101_,
                v_skipInstances_8102_,
                v_x_8103_,
                v_x_8104_,
                v___x_8140_,
                v_a_8107_,
            );
        v___x_8142_ = leanh::lean_apply_4(
            v_toBind_8133_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_8141_,
            v___f_8139_,
        );
        return v___x_8142_;
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(
    mut v_expr_8143_: *mut leanh::LeanObject,
    mut v_data_8144_: *mut leanh::LeanObject,
    mut v_inst_8145_: *mut leanh::LeanObject,
    mut v_inst_8146_: *mut leanh::LeanObject,
    mut v_inst_8147_: *mut leanh::LeanObject,
    mut v_pre_8148_: *mut leanh::LeanObject,
    mut v_post_8149_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8150_: u8,
    mut v_skipConstInApp_8151_: u8,
    mut v_skipInstances_8152_: u8,
    mut v_x_8153_: *mut leanh::LeanObject,
    mut v_x_8154_: *mut leanh::LeanObject,
    mut v___y_8155_: *mut leanh::LeanObject,
    mut v___y_8156_: *mut leanh::LeanObject,
    mut v_a_8157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8158_: usize = 0;
    let mut v___x_8159_: usize = 0;
    let mut v___x_8160_: u8 = 0;
    v___x_8158_ = lean_ptr_addr(v_expr_8143_);
    v___x_8159_ = lean_ptr_addr(v_a_8157_);
    v___x_8160_ = lean_usize_dec_eq(v___x_8158_, v___x_8159_);
    if v___x_8160_ == 0 {
        let mut v___x_8161_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8162_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___y_8156_);
        v___x_8161_ = l_Lean_Expr_mdata___override(v_data_8144_, v_a_8157_);
        v___x_8162_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_8145_, v_inst_8146_, v_inst_8147_, v_pre_8148_, v_post_8149_, v_usedLetOnly_8150_, v_skipConstInApp_8151_, v_skipInstances_8152_, v_x_8153_, v_x_8154_, v___x_8161_, v___y_8155_);
        return v___x_8162_;
    } else {
        let mut v___x_8163_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_a_8157_);
        leanh::lean_dec(v_data_8144_);
        v___x_8163_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_8145_, v_inst_8146_, v_inst_8147_, v_pre_8148_, v_post_8149_, v_usedLetOnly_8150_, v_skipConstInApp_8151_, v_skipInstances_8152_, v_x_8153_, v_x_8154_, v___y_8156_, v___y_8155_);
        return v___x_8163_;
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed(
    mut v_expr_8164_: *mut leanh::LeanObject,
    mut v_data_8165_: *mut leanh::LeanObject,
    mut v_inst_8166_: *mut leanh::LeanObject,
    mut v_inst_8167_: *mut leanh::LeanObject,
    mut v_inst_8168_: *mut leanh::LeanObject,
    mut v_pre_8169_: *mut leanh::LeanObject,
    mut v_post_8170_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8171_: *mut leanh::LeanObject,
    mut v_skipConstInApp_8172_: *mut leanh::LeanObject,
    mut v_skipInstances_8173_: *mut leanh::LeanObject,
    mut v_x_8174_: *mut leanh::LeanObject,
    mut v_x_8175_: *mut leanh::LeanObject,
    mut v___y_8176_: *mut leanh::LeanObject,
    mut v___y_8177_: *mut leanh::LeanObject,
    mut v_a_8178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_8179_: u8 = 0;
    let mut v_skipConstInApp_boxed_8180_: u8 = 0;
    let mut v_skipInstances_boxed_8181_: u8 = 0;
    let mut v_res_8182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_8179_ = (leanh::lean_unbox(v_usedLetOnly_8171_) as u8);
    v_skipConstInApp_boxed_8180_ = (leanh::lean_unbox(v_skipConstInApp_8172_) as u8);
    v_skipInstances_boxed_8181_ = (leanh::lean_unbox(v_skipInstances_8173_) as u8);
    v_res_8182_ =
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(
            v_expr_8164_,
            v_data_8165_,
            v_inst_8166_,
            v_inst_8167_,
            v_inst_8168_,
            v_pre_8169_,
            v_post_8170_,
            v_usedLetOnly_boxed_8179_,
            v_skipConstInApp_boxed_8180_,
            v_skipInstances_boxed_8181_,
            v_x_8174_,
            v_x_8175_,
            v___y_8176_,
            v___y_8177_,
            v_a_8178_,
        );
    leanh::lean_dec(v___y_8176_);
    leanh::lean_dec_ref(v_expr_8164_);
    return v_res_8182_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(
    mut v_struct_8183_: *mut leanh::LeanObject,
    mut v_typeName_8184_: *mut leanh::LeanObject,
    mut v_idx_8185_: *mut leanh::LeanObject,
    mut v_inst_8186_: *mut leanh::LeanObject,
    mut v_inst_8187_: *mut leanh::LeanObject,
    mut v_inst_8188_: *mut leanh::LeanObject,
    mut v_pre_8189_: *mut leanh::LeanObject,
    mut v_post_8190_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8191_: u8,
    mut v_skipConstInApp_8192_: u8,
    mut v_skipInstances_8193_: u8,
    mut v_x_8194_: *mut leanh::LeanObject,
    mut v_x_8195_: *mut leanh::LeanObject,
    mut v___y_8196_: *mut leanh::LeanObject,
    mut v___y_8197_: *mut leanh::LeanObject,
    mut v_a_8198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8199_: usize = 0;
    let mut v___x_8200_: usize = 0;
    let mut v___x_8201_: u8 = 0;
    v___x_8199_ = lean_ptr_addr(v_struct_8183_);
    v___x_8200_ = lean_ptr_addr(v_a_8198_);
    v___x_8201_ = lean_usize_dec_eq(v___x_8199_, v___x_8200_);
    if v___x_8201_ == 0 {
        let mut v___x_8202_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8203_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___y_8197_);
        v___x_8202_ = l_Lean_Expr_proj___override(v_typeName_8184_, v_idx_8185_, v_a_8198_);
        v___x_8203_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_8186_, v_inst_8187_, v_inst_8188_, v_pre_8189_, v_post_8190_, v_usedLetOnly_8191_, v_skipConstInApp_8192_, v_skipInstances_8193_, v_x_8194_, v_x_8195_, v___x_8202_, v___y_8196_);
        return v___x_8203_;
    } else {
        let mut v___x_8204_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_a_8198_);
        leanh::lean_dec(v_idx_8185_);
        leanh::lean_dec(v_typeName_8184_);
        v___x_8204_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_8186_, v_inst_8187_, v_inst_8188_, v_pre_8189_, v_post_8190_, v_usedLetOnly_8191_, v_skipConstInApp_8192_, v_skipInstances_8193_, v_x_8194_, v_x_8195_, v___y_8197_, v___y_8196_);
        return v___x_8204_;
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed(
    mut v_struct_8205_: *mut leanh::LeanObject,
    mut v_typeName_8206_: *mut leanh::LeanObject,
    mut v_idx_8207_: *mut leanh::LeanObject,
    mut v_inst_8208_: *mut leanh::LeanObject,
    mut v_inst_8209_: *mut leanh::LeanObject,
    mut v_inst_8210_: *mut leanh::LeanObject,
    mut v_pre_8211_: *mut leanh::LeanObject,
    mut v_post_8212_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8213_: *mut leanh::LeanObject,
    mut v_skipConstInApp_8214_: *mut leanh::LeanObject,
    mut v_skipInstances_8215_: *mut leanh::LeanObject,
    mut v_x_8216_: *mut leanh::LeanObject,
    mut v_x_8217_: *mut leanh::LeanObject,
    mut v___y_8218_: *mut leanh::LeanObject,
    mut v___y_8219_: *mut leanh::LeanObject,
    mut v_a_8220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_8221_: u8 = 0;
    let mut v_skipConstInApp_boxed_8222_: u8 = 0;
    let mut v_skipInstances_boxed_8223_: u8 = 0;
    let mut v_res_8224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_8221_ = (leanh::lean_unbox(v_usedLetOnly_8213_) as u8);
    v_skipConstInApp_boxed_8222_ = (leanh::lean_unbox(v_skipConstInApp_8214_) as u8);
    v_skipInstances_boxed_8223_ = (leanh::lean_unbox(v_skipInstances_8215_) as u8);
    v_res_8224_ =
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(
            v_struct_8205_,
            v_typeName_8206_,
            v_idx_8207_,
            v_inst_8208_,
            v_inst_8209_,
            v_inst_8210_,
            v_pre_8211_,
            v_post_8212_,
            v_usedLetOnly_boxed_8221_,
            v_skipConstInApp_boxed_8222_,
            v_skipInstances_boxed_8223_,
            v_x_8216_,
            v_x_8217_,
            v___y_8218_,
            v___y_8219_,
            v_a_8220_,
        );
    leanh::lean_dec(v___y_8218_);
    leanh::lean_dec_ref(v_struct_8205_);
    return v_res_8224_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(
    mut v_toApplicative_8225_: *mut leanh::LeanObject,
    mut v_inst_8226_: *mut leanh::LeanObject,
    mut v_inst_8227_: *mut leanh::LeanObject,
    mut v_inst_8228_: *mut leanh::LeanObject,
    mut v_pre_8229_: *mut leanh::LeanObject,
    mut v_post_8230_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8231_: u8,
    mut v_skipConstInApp_8232_: u8,
    mut v_skipInstances_8233_: u8,
    mut v_x_8234_: *mut leanh::LeanObject,
    mut v_x_8235_: *mut leanh::LeanObject,
    mut v___y_8236_: *mut leanh::LeanObject,
    mut v___f_8237_: *mut leanh::LeanObject,
    mut v_toBind_8238_: *mut leanh::LeanObject,
    mut v_e_8239_: *mut leanh::LeanObject,
    mut v_a_8240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_8242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_8249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_8250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755__overap_8254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_8256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_8257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_8264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_8265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_8266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_8274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_8275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_8277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_8279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_a_8240_) {
                0 => {
                    leanh::lean_dec_ref(v_e_8239_);
                    leanh::lean_dec(v_toBind_8238_);
                    leanh::lean_dec(v___f_8237_);
                    leanh::lean_dec(v_x_8235_);
                    leanh::lean_dec(v_post_8230_);
                    leanh::lean_dec(v_pre_8229_);
                    leanh::lean_dec_ref(v_inst_8228_);
                    leanh::lean_dec(v_inst_8227_);
                    leanh::lean_dec_ref(v_inst_8226_);
                    v_e_8274_ = leanh::lean_ctor_get(v_a_8240_, 0);
                    leanh::lean_inc_ref(v_e_8274_);
                    leanh::lean_dec_ref_known(v_a_8240_, 1);
                    v_toPure_8275_ = leanh::lean_ctor_get(v_toApplicative_8225_, 1);
                    leanh::lean_inc(v_toPure_8275_);
                    leanh::lean_dec_ref(v_toApplicative_8225_);
                    v___x_8276_ = leanh::lean_apply_2(
                        v_toPure_8275_,
                        leanh::lean_box(0),
                        v_e_8274_,
                    );
                    return v___x_8276_;
                }
                1 => {
                    leanh::lean_dec_ref(v_e_8239_);
                    leanh::lean_dec(v_toBind_8238_);
                    leanh::lean_dec(v___f_8237_);
                    leanh::lean_dec_ref(v_toApplicative_8225_);
                    v_e_8277_ = leanh::lean_ctor_get(v_a_8240_, 0);
                    leanh::lean_inc_ref(v_e_8277_);
                    leanh::lean_dec_ref_known(v_a_8240_, 1);
                    v___x_8278_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_8226_, v_inst_8227_, v_inst_8228_, v_pre_8229_, v_post_8230_, v_usedLetOnly_8231_, v_skipConstInApp_8232_, v_skipInstances_8233_, v_x_8234_, v_x_8235_, v_e_8277_, v___y_8236_);
                    return v___x_8278_;
                }
                _ => {
                    leanh::lean_dec_ref(v_toApplicative_8225_);
                    v_e_x3f_8279_ = leanh::lean_ctor_get(v_a_8240_, 0);
                    leanh::lean_inc(v_e_x3f_8279_);
                    leanh::lean_dec_ref_known(v_a_8240_, 1);
                    if leanh::lean_obj_tag(v_e_x3f_8279_) == 0 {
                        v___y_8242_ = v_e_8239_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_e_8239_);
                        v_val_8280_ = leanh::lean_ctor_get(v_e_x3f_8279_, 0);
                        leanh::lean_inc(v_val_8280_);
                        leanh::lean_dec_ref_known(v_e_x3f_8279_, 1);
                        v___y_8242_ = v_val_8280_;
                        state = 1;
                        continue;
                    }
                }
            },
            1 => match leanh::lean_obj_tag(v___y_8242_) {
                7 => {
                    leanh::lean_dec(v_toBind_8238_);
                    leanh::lean_dec(v___f_8237_);
                    v___x_8243_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0;
                    v___x_8244_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_8226_, v_inst_8227_, v_inst_8228_, v_pre_8229_, v_post_8230_, v_usedLetOnly_8231_, v_skipConstInApp_8232_, v_skipInstances_8233_, v_x_8234_, v_x_8235_, v___x_8243_, v___y_8242_, v___y_8236_);
                    return v___x_8244_;
                }
                6 => {
                    leanh::lean_dec(v_toBind_8238_);
                    leanh::lean_dec(v___f_8237_);
                    v___x_8245_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0;
                    v___x_8246_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_8226_, v_inst_8227_, v_inst_8228_, v_pre_8229_, v_post_8230_, v_usedLetOnly_8231_, v_skipConstInApp_8232_, v_skipInstances_8233_, v_x_8234_, v_x_8235_, v___x_8245_, v___y_8242_, v___y_8236_);
                    return v___x_8246_;
                }
                8 => {
                    leanh::lean_dec(v_toBind_8238_);
                    leanh::lean_dec(v___f_8237_);
                    v___x_8247_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0;
                    v___x_8248_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_8226_, v_inst_8227_, v_inst_8228_, v_pre_8229_, v_post_8230_, v_usedLetOnly_8231_, v_skipConstInApp_8232_, v_skipInstances_8233_, v_x_8234_, v_x_8235_, v___x_8247_, v___y_8242_, v___y_8236_);
                    return v___x_8248_;
                }
                5 => {
                    leanh::lean_dec(v_toBind_8238_);
                    leanh::lean_dec(v_x_8235_);
                    leanh::lean_dec(v_post_8230_);
                    leanh::lean_dec(v_pre_8229_);
                    leanh::lean_dec_ref(v_inst_8228_);
                    leanh::lean_dec(v_inst_8227_);
                    leanh::lean_dec_ref(v_inst_8226_);
                    v_dummy_8249_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once), _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
                    v_nargs_8250_ = l_Lean_Expr_getAppNumArgs(v___y_8242_);
                    leanh::lean_inc(v_nargs_8250_);
                    v___x_8251_ = lean_mk_array(v_nargs_8250_, v_dummy_8249_);
                    v___x_8252_ = leanh::lean_unsigned_to_nat(1);
                    v___x_8253_ = lean_nat_sub(v_nargs_8250_, v___x_8252_);
                    leanh::lean_dec(v_nargs_8250_);
                    v___x_3755__overap_8254_ = l_Lean_Expr_withAppAux___redArg(
                        v___f_8237_,
                        v___y_8242_,
                        v___x_8251_,
                        v___x_8253_,
                    );
                    leanh::lean_inc(v___y_8236_);
                    v___x_8255_ = leanh::lean_apply_1(v___x_3755__overap_8254_, v___y_8236_);
                    return v___x_8255_;
                }
                10 => {
                    leanh::lean_dec(v___f_8237_);
                    v_data_8256_ = leanh::lean_ctor_get(v___y_8242_, 0);
                    leanh::lean_inc(v_data_8256_);
                    v_expr_8257_ = leanh::lean_ctor_get(v___y_8242_, 1);
                    leanh::lean_inc_ref_n(v_expr_8257_, 2);
                    v___x_8258_ = leanh::lean_box((v_usedLetOnly_8231_) as usize);
                    v___x_8259_ = leanh::lean_box((v_skipConstInApp_8232_) as usize);
                    v___x_8260_ = leanh::lean_box((v_skipInstances_8233_) as usize);
                    leanh::lean_inc(v___y_8236_);
                    leanh::lean_inc(v_x_8235_);
                    leanh::lean_inc(v_post_8230_);
                    leanh::lean_inc(v_pre_8229_);
                    leanh::lean_inc_ref(v_inst_8228_);
                    leanh::lean_inc(v_inst_8227_);
                    leanh::lean_inc_ref(v_inst_8226_);
                    v___f_8261_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed as *mut core::ffi::c_void, 15, 14);
                    leanh::lean_closure_set(v___f_8261_, 0, v_expr_8257_);
                    leanh::lean_closure_set(v___f_8261_, 1, v_data_8256_);
                    leanh::lean_closure_set(v___f_8261_, 2, v_inst_8226_);
                    leanh::lean_closure_set(v___f_8261_, 3, v_inst_8227_);
                    leanh::lean_closure_set(v___f_8261_, 4, v_inst_8228_);
                    leanh::lean_closure_set(v___f_8261_, 5, v_pre_8229_);
                    leanh::lean_closure_set(v___f_8261_, 6, v_post_8230_);
                    leanh::lean_closure_set(v___f_8261_, 7, v___x_8258_);
                    leanh::lean_closure_set(v___f_8261_, 8, v___x_8259_);
                    leanh::lean_closure_set(v___f_8261_, 9, v___x_8260_);
                    leanh::lean_closure_set(v___f_8261_, 10, v_x_8234_);
                    leanh::lean_closure_set(v___f_8261_, 11, v_x_8235_);
                    leanh::lean_closure_set(v___f_8261_, 12, v___y_8236_);
                    leanh::lean_closure_set(v___f_8261_, 13, v___y_8242_);
                    v___x_8262_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_8226_, v_inst_8227_, v_inst_8228_, v_pre_8229_, v_post_8230_, v_usedLetOnly_8231_, v_skipConstInApp_8232_, v_skipInstances_8233_, v_x_8234_, v_x_8235_, v_expr_8257_, v___y_8236_);
                    v___x_8263_ = leanh::lean_apply_4(
                        v_toBind_8238_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_8262_,
                        v___f_8261_,
                    );
                    return v___x_8263_;
                }
                11 => {
                    leanh::lean_dec(v___f_8237_);
                    v_typeName_8264_ = leanh::lean_ctor_get(v___y_8242_, 0);
                    leanh::lean_inc(v_typeName_8264_);
                    v_idx_8265_ = leanh::lean_ctor_get(v___y_8242_, 1);
                    leanh::lean_inc(v_idx_8265_);
                    v_struct_8266_ = leanh::lean_ctor_get(v___y_8242_, 2);
                    leanh::lean_inc_ref_n(v_struct_8266_, 2);
                    v___x_8267_ = leanh::lean_box((v_usedLetOnly_8231_) as usize);
                    v___x_8268_ = leanh::lean_box((v_skipConstInApp_8232_) as usize);
                    v___x_8269_ = leanh::lean_box((v_skipInstances_8233_) as usize);
                    leanh::lean_inc(v___y_8236_);
                    leanh::lean_inc(v_x_8235_);
                    leanh::lean_inc(v_post_8230_);
                    leanh::lean_inc(v_pre_8229_);
                    leanh::lean_inc_ref(v_inst_8228_);
                    leanh::lean_inc(v_inst_8227_);
                    leanh::lean_inc_ref(v_inst_8226_);
                    v___f_8270_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed as *mut core::ffi::c_void, 16, 15);
                    leanh::lean_closure_set(v___f_8270_, 0, v_struct_8266_);
                    leanh::lean_closure_set(v___f_8270_, 1, v_typeName_8264_);
                    leanh::lean_closure_set(v___f_8270_, 2, v_idx_8265_);
                    leanh::lean_closure_set(v___f_8270_, 3, v_inst_8226_);
                    leanh::lean_closure_set(v___f_8270_, 4, v_inst_8227_);
                    leanh::lean_closure_set(v___f_8270_, 5, v_inst_8228_);
                    leanh::lean_closure_set(v___f_8270_, 6, v_pre_8229_);
                    leanh::lean_closure_set(v___f_8270_, 7, v_post_8230_);
                    leanh::lean_closure_set(v___f_8270_, 8, v___x_8267_);
                    leanh::lean_closure_set(v___f_8270_, 9, v___x_8268_);
                    leanh::lean_closure_set(v___f_8270_, 10, v___x_8269_);
                    leanh::lean_closure_set(v___f_8270_, 11, v_x_8234_);
                    leanh::lean_closure_set(v___f_8270_, 12, v_x_8235_);
                    leanh::lean_closure_set(v___f_8270_, 13, v___y_8236_);
                    leanh::lean_closure_set(v___f_8270_, 14, v___y_8242_);
                    v___x_8271_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_8226_, v_inst_8227_, v_inst_8228_, v_pre_8229_, v_post_8230_, v_usedLetOnly_8231_, v_skipConstInApp_8232_, v_skipInstances_8233_, v_x_8234_, v_x_8235_, v_struct_8266_, v___y_8236_);
                    v___x_8272_ = leanh::lean_apply_4(
                        v_toBind_8238_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_8271_,
                        v___f_8270_,
                    );
                    return v___x_8272_;
                }
                _ => {
                    leanh::lean_dec(v_toBind_8238_);
                    leanh::lean_dec(v___f_8237_);
                    v___x_8273_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_8226_, v_inst_8227_, v_inst_8228_, v_pre_8229_, v_post_8230_, v_usedLetOnly_8231_, v_skipConstInApp_8232_, v_skipInstances_8233_, v_x_8234_, v_x_8235_, v___y_8242_, v___y_8236_);
                    return v___x_8273_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed(
    mut v_toApplicative_8281_: *mut leanh::LeanObject,
    mut v_inst_8282_: *mut leanh::LeanObject,
    mut v_inst_8283_: *mut leanh::LeanObject,
    mut v_inst_8284_: *mut leanh::LeanObject,
    mut v_pre_8285_: *mut leanh::LeanObject,
    mut v_post_8286_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8287_: *mut leanh::LeanObject,
    mut v_skipConstInApp_8288_: *mut leanh::LeanObject,
    mut v_skipInstances_8289_: *mut leanh::LeanObject,
    mut v_x_8290_: *mut leanh::LeanObject,
    mut v_x_8291_: *mut leanh::LeanObject,
    mut v___y_8292_: *mut leanh::LeanObject,
    mut v___f_8293_: *mut leanh::LeanObject,
    mut v_toBind_8294_: *mut leanh::LeanObject,
    mut v_e_8295_: *mut leanh::LeanObject,
    mut v_a_8296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_8297_: u8 = 0;
    let mut v_skipConstInApp_boxed_8298_: u8 = 0;
    let mut v_skipInstances_boxed_8299_: u8 = 0;
    let mut v_res_8300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_8297_ = (leanh::lean_unbox(v_usedLetOnly_8287_) as u8);
    v_skipConstInApp_boxed_8298_ = (leanh::lean_unbox(v_skipConstInApp_8288_) as u8);
    v_skipInstances_boxed_8299_ = (leanh::lean_unbox(v_skipInstances_8289_) as u8);
    v_res_8300_ =
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(
            v_toApplicative_8281_,
            v_inst_8282_,
            v_inst_8283_,
            v_inst_8284_,
            v_pre_8285_,
            v_post_8286_,
            v_usedLetOnly_boxed_8297_,
            v_skipConstInApp_boxed_8298_,
            v_skipInstances_boxed_8299_,
            v_x_8290_,
            v_x_8291_,
            v___y_8292_,
            v___f_8293_,
            v_toBind_8294_,
            v_e_8295_,
            v_a_8296_,
        );
    leanh::lean_dec(v___y_8292_);
    return v_res_8300_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(
    mut v_toApplicative_8301_: *mut leanh::LeanObject,
    mut v_inst_8302_: *mut leanh::LeanObject,
    mut v_inst_8303_: *mut leanh::LeanObject,
    mut v_inst_8304_: *mut leanh::LeanObject,
    mut v_pre_8305_: *mut leanh::LeanObject,
    mut v_post_8306_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8307_: u8,
    mut v_skipConstInApp_8308_: u8,
    mut v_skipInstances_8309_: u8,
    mut v_x_8310_: *mut leanh::LeanObject,
    mut v_x_8311_: *mut leanh::LeanObject,
    mut v___f_8312_: *mut leanh::LeanObject,
    mut v_toBind_8313_: *mut leanh::LeanObject,
    mut v_e_8314_: *mut leanh::LeanObject,
    mut v_____r_8315_: *mut leanh::LeanObject,
    mut v___y_8316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8317_ = leanh::lean_box((v_usedLetOnly_8307_) as usize);
    v___x_8318_ = leanh::lean_box((v_skipConstInApp_8308_) as usize);
    v___x_8319_ = leanh::lean_box((v_skipInstances_8309_) as usize);
    leanh::lean_inc_ref(v_e_8314_);
    leanh::lean_inc(v_toBind_8313_);
    leanh::lean_inc(v___y_8316_);
    leanh::lean_inc(v_pre_8305_);
    v___f_8320_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed as *mut core::ffi::c_void, 16, 15);
    leanh::lean_closure_set(v___f_8320_, 0, v_toApplicative_8301_);
    leanh::lean_closure_set(v___f_8320_, 1, v_inst_8302_);
    leanh::lean_closure_set(v___f_8320_, 2, v_inst_8303_);
    leanh::lean_closure_set(v___f_8320_, 3, v_inst_8304_);
    leanh::lean_closure_set(v___f_8320_, 4, v_pre_8305_);
    leanh::lean_closure_set(v___f_8320_, 5, v_post_8306_);
    leanh::lean_closure_set(v___f_8320_, 6, v___x_8317_);
    leanh::lean_closure_set(v___f_8320_, 7, v___x_8318_);
    leanh::lean_closure_set(v___f_8320_, 8, v___x_8319_);
    leanh::lean_closure_set(v___f_8320_, 9, v_x_8310_);
    leanh::lean_closure_set(v___f_8320_, 10, v_x_8311_);
    leanh::lean_closure_set(v___f_8320_, 11, v___y_8316_);
    leanh::lean_closure_set(v___f_8320_, 12, v___f_8312_);
    leanh::lean_closure_set(v___f_8320_, 13, v_toBind_8313_);
    leanh::lean_closure_set(v___f_8320_, 14, v_e_8314_);
    v___x_8321_ = leanh::lean_apply_1(v_pre_8305_, v_e_8314_);
    v___x_8322_ = leanh::lean_apply_4(
        v_toBind_8313_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_8321_,
        v___f_8320_,
    );
    return v___x_8322_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed(
    mut v_toApplicative_8323_: *mut leanh::LeanObject,
    mut v_inst_8324_: *mut leanh::LeanObject,
    mut v_inst_8325_: *mut leanh::LeanObject,
    mut v_inst_8326_: *mut leanh::LeanObject,
    mut v_pre_8327_: *mut leanh::LeanObject,
    mut v_post_8328_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8329_: *mut leanh::LeanObject,
    mut v_skipConstInApp_8330_: *mut leanh::LeanObject,
    mut v_skipInstances_8331_: *mut leanh::LeanObject,
    mut v_x_8332_: *mut leanh::LeanObject,
    mut v_x_8333_: *mut leanh::LeanObject,
    mut v___f_8334_: *mut leanh::LeanObject,
    mut v_toBind_8335_: *mut leanh::LeanObject,
    mut v_e_8336_: *mut leanh::LeanObject,
    mut v_____r_8337_: *mut leanh::LeanObject,
    mut v___y_8338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_8339_: u8 = 0;
    let mut v_skipConstInApp_boxed_8340_: u8 = 0;
    let mut v_skipInstances_boxed_8341_: u8 = 0;
    let mut v_res_8342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_8339_ = (leanh::lean_unbox(v_usedLetOnly_8329_) as u8);
    v_skipConstInApp_boxed_8340_ = (leanh::lean_unbox(v_skipConstInApp_8330_) as u8);
    v_skipInstances_boxed_8341_ = (leanh::lean_unbox(v_skipInstances_8331_) as u8);
    v_res_8342_ =
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(
            v_toApplicative_8323_,
            v_inst_8324_,
            v_inst_8325_,
            v_inst_8326_,
            v_pre_8327_,
            v_post_8328_,
            v_usedLetOnly_boxed_8339_,
            v_skipConstInApp_boxed_8340_,
            v_skipInstances_boxed_8341_,
            v_x_8332_,
            v_x_8333_,
            v___f_8334_,
            v_toBind_8335_,
            v_e_8336_,
            v_____r_8337_,
            v___y_8338_,
        );
    leanh::lean_dec(v___y_8338_);
    return v_res_8342_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(
    mut v_inst_8343_: *mut leanh::LeanObject,
    mut v_inst_8344_: *mut leanh::LeanObject,
    mut v_inst_8345_: *mut leanh::LeanObject,
    mut v_pre_8346_: *mut leanh::LeanObject,
    mut v_post_8347_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8348_: u8,
    mut v_skipConstInApp_8349_: u8,
    mut v_skipInstances_8350_: u8,
    mut v_x_8351_: *mut leanh::LeanObject,
    mut v_x_8352_: *mut leanh::LeanObject,
    mut v_e_8353_: *mut leanh::LeanObject,
    mut v_a_8354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_8362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_8363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8355_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0;
    v___x_8356_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1;
    leanh::lean_inc_ref_n(v_inst_8343_, 3);
    v___x_8357_ =
        l_Lean_MonadCacheT_instMonad___redArg(v_x_8351_, v___x_8355_, v___x_8356_, v_inst_8343_);
    v___x_8358_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_8351_, v___x_8355_, v___x_8356_);
    leanh::lean_inc_ref_n(v_inst_8345_, 3);
    leanh::lean_inc_ref(v___x_8358_);
    v___f_8359_ = leanh::lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__3 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_8359_, 0, v___x_8358_);
    leanh::lean_closure_set(v___f_8359_, 1, v_inst_8345_);
    v___f_8360_ = leanh::lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__4 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_8360_, 0, v___x_8358_);
    leanh::lean_closure_set(v___f_8360_, 1, v_inst_8345_);
    v___x_8361_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_8361_, 0, v___f_8359_);
    leanh::lean_ctor_set(v___x_8361_, 1, v___f_8360_);
    v_toApplicative_8362_ = leanh::lean_ctor_get(v_inst_8343_, 0);
    leanh::lean_inc_ref_n(v_toApplicative_8362_, 6);
    v_toBind_8363_ = leanh::lean_ctor_get(v_inst_8343_, 1);
    leanh::lean_inc_n(v_toBind_8363_, 6);
    v___f_8364_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_8364_, 0, v_toApplicative_8362_);
    leanh::lean_inc_n(v_x_8352_, 3);
    leanh::lean_inc_n(v_a_8354_, 3);
    leanh::lean_inc_ref_n(v_e_8353_, 2);
    v___f_8365_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2___boxed
            as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_8365_, 0, v_toApplicative_8362_);
    leanh::lean_closure_set(v___f_8365_, 1, v___x_8355_);
    leanh::lean_closure_set(v___f_8365_, 2, v___x_8356_);
    leanh::lean_closure_set(v___f_8365_, 3, v_e_8353_);
    leanh::lean_closure_set(v___f_8365_, 4, v_a_8354_);
    leanh::lean_closure_set(v___f_8365_, 5, v_x_8352_);
    leanh::lean_closure_set(v___f_8365_, 6, v_toBind_8363_);
    v___f_8366_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_8366_, 0, v_toApplicative_8362_);
    leanh::lean_closure_set(v___f_8366_, 1, v___x_8355_);
    leanh::lean_closure_set(v___f_8366_, 2, v___x_8356_);
    leanh::lean_closure_set(v___f_8366_, 3, v_e_8353_);
    v___x_8367_ = leanh::lean_box((v_skipInstances_8350_) as usize);
    v___x_8368_ = leanh::lean_box((v_usedLetOnly_8348_) as usize);
    v___x_8369_ = leanh::lean_box((v_skipConstInApp_8349_) as usize);
    leanh::lean_inc_ref(v___x_8357_);
    leanh::lean_inc(v_post_8347_);
    leanh::lean_inc(v_pre_8346_);
    leanh::lean_inc_n(v_inst_8344_, 2);
    v___f_8370_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed as *mut core::ffi::c_void, 17, 14);
    leanh::lean_closure_set(v___f_8370_, 0, v___x_8367_);
    leanh::lean_closure_set(v___f_8370_, 1, v_inst_8343_);
    leanh::lean_closure_set(v___f_8370_, 2, v_inst_8344_);
    leanh::lean_closure_set(v___f_8370_, 3, v_inst_8345_);
    leanh::lean_closure_set(v___f_8370_, 4, v_pre_8346_);
    leanh::lean_closure_set(v___f_8370_, 5, v_post_8347_);
    leanh::lean_closure_set(v___f_8370_, 6, v___x_8368_);
    leanh::lean_closure_set(v___f_8370_, 7, v___x_8369_);
    leanh::lean_closure_set(v___f_8370_, 8, v_x_8351_);
    leanh::lean_closure_set(v___f_8370_, 9, v_x_8352_);
    leanh::lean_closure_set(v___f_8370_, 10, v___x_8357_);
    leanh::lean_closure_set(v___f_8370_, 11, v_toBind_8363_);
    leanh::lean_closure_set(v___f_8370_, 12, v_toApplicative_8362_);
    leanh::lean_closure_set(v___f_8370_, 13, v___f_8364_);
    v___x_8371_ = leanh::lean_box((v_usedLetOnly_8348_) as usize);
    v___x_8372_ = leanh::lean_box((v_skipConstInApp_8349_) as usize);
    v___x_8373_ = leanh::lean_box((v_skipInstances_8350_) as usize);
    v___f_8374_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed as *mut core::ffi::c_void, 16, 14);
    leanh::lean_closure_set(v___f_8374_, 0, v_toApplicative_8362_);
    leanh::lean_closure_set(v___f_8374_, 1, v_inst_8343_);
    leanh::lean_closure_set(v___f_8374_, 2, v_inst_8344_);
    leanh::lean_closure_set(v___f_8374_, 3, v_inst_8345_);
    leanh::lean_closure_set(v___f_8374_, 4, v_pre_8346_);
    leanh::lean_closure_set(v___f_8374_, 5, v_post_8347_);
    leanh::lean_closure_set(v___f_8374_, 6, v___x_8371_);
    leanh::lean_closure_set(v___f_8374_, 7, v___x_8372_);
    leanh::lean_closure_set(v___f_8374_, 8, v___x_8373_);
    leanh::lean_closure_set(v___f_8374_, 9, v_x_8351_);
    leanh::lean_closure_set(v___f_8374_, 10, v_x_8352_);
    leanh::lean_closure_set(v___f_8374_, 11, v___f_8370_);
    leanh::lean_closure_set(v___f_8374_, 12, v_toBind_8363_);
    leanh::lean_closure_set(v___f_8374_, 13, v_e_8353_);
    v___f_8375_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed as *mut core::ffi::c_void, 13, 12);
    leanh::lean_closure_set(v___f_8375_, 0, v_inst_8344_);
    leanh::lean_closure_set(v___f_8375_, 1, v_x_8351_);
    leanh::lean_closure_set(v___f_8375_, 2, v___x_8355_);
    leanh::lean_closure_set(v___f_8375_, 3, v___x_8356_);
    leanh::lean_closure_set(v___f_8375_, 4, v_inst_8343_);
    leanh::lean_closure_set(v___f_8375_, 5, v___f_8374_);
    leanh::lean_closure_set(v___f_8375_, 6, v___x_8361_);
    leanh::lean_closure_set(v___f_8375_, 7, v___x_8357_);
    leanh::lean_closure_set(v___f_8375_, 8, v_a_8354_);
    leanh::lean_closure_set(v___f_8375_, 9, v_toBind_8363_);
    leanh::lean_closure_set(v___f_8375_, 10, v___f_8365_);
    leanh::lean_closure_set(v___f_8375_, 11, v_toApplicative_8362_);
    v___x_8376_ =
        leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_8376_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_8376_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_8376_, 2, v_a_8354_);
    v___x_8377_ = leanh::lean_apply_2(v_x_8352_, leanh::lean_box(0), v___x_8376_);
    v___x_8378_ = leanh::lean_apply_4(
        v_toBind_8363_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_8377_,
        v___f_8366_,
    );
    v___x_8379_ = leanh::lean_apply_4(
        v_toBind_8363_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_8378_,
        v___f_8375_,
    );
    return v___x_8379_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(
    mut v_toApplicative_8380_: *mut leanh::LeanObject,
    mut v_inst_8381_: *mut leanh::LeanObject,
    mut v_inst_8382_: *mut leanh::LeanObject,
    mut v_inst_8383_: *mut leanh::LeanObject,
    mut v_pre_8384_: *mut leanh::LeanObject,
    mut v_post_8385_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8386_: u8,
    mut v_skipConstInApp_8387_: u8,
    mut v_skipInstances_8388_: u8,
    mut v_x_8389_: *mut leanh::LeanObject,
    mut v_x_8390_: *mut leanh::LeanObject,
    mut v_a_8391_: *mut leanh::LeanObject,
    mut v_e_8392_: *mut leanh::LeanObject,
    mut v_a_8393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_8395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_8396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_8398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_8399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_8401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_8403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_a_8393_) {
                0 => {
                    leanh::lean_dec_ref(v_e_8392_);
                    leanh::lean_dec(v_x_8390_);
                    leanh::lean_dec(v_post_8385_);
                    leanh::lean_dec(v_pre_8384_);
                    leanh::lean_dec_ref(v_inst_8383_);
                    leanh::lean_dec(v_inst_8382_);
                    leanh::lean_dec_ref(v_inst_8381_);
                    v_e_8398_ = leanh::lean_ctor_get(v_a_8393_, 0);
                    leanh::lean_inc_ref(v_e_8398_);
                    leanh::lean_dec_ref_known(v_a_8393_, 1);
                    v_toPure_8399_ = leanh::lean_ctor_get(v_toApplicative_8380_, 1);
                    leanh::lean_inc(v_toPure_8399_);
                    leanh::lean_dec_ref(v_toApplicative_8380_);
                    v___x_8400_ = leanh::lean_apply_2(
                        v_toPure_8399_,
                        leanh::lean_box(0),
                        v_e_8398_,
                    );
                    return v___x_8400_;
                }
                1 => {
                    leanh::lean_dec_ref(v_e_8392_);
                    leanh::lean_dec_ref(v_toApplicative_8380_);
                    v_e_8401_ = leanh::lean_ctor_get(v_a_8393_, 0);
                    leanh::lean_inc_ref(v_e_8401_);
                    leanh::lean_dec_ref_known(v_a_8393_, 1);
                    v___x_8402_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_8381_, v_inst_8382_, v_inst_8383_, v_pre_8384_, v_post_8385_, v_usedLetOnly_8386_, v_skipConstInApp_8387_, v_skipInstances_8388_, v_x_8389_, v_x_8390_, v_e_8401_, v_a_8391_);
                    return v___x_8402_;
                }
                _ => {
                    leanh::lean_dec(v_x_8390_);
                    leanh::lean_dec(v_post_8385_);
                    leanh::lean_dec(v_pre_8384_);
                    leanh::lean_dec_ref(v_inst_8383_);
                    leanh::lean_dec(v_inst_8382_);
                    leanh::lean_dec_ref(v_inst_8381_);
                    v_e_x3f_8403_ = leanh::lean_ctor_get(v_a_8393_, 0);
                    leanh::lean_inc(v_e_x3f_8403_);
                    leanh::lean_dec_ref_known(v_a_8393_, 1);
                    if leanh::lean_obj_tag(v_e_x3f_8403_) == 0 {
                        v___y_8395_ = v_e_8392_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_e_8392_);
                        v_val_8404_ = leanh::lean_ctor_get(v_e_x3f_8403_, 0);
                        leanh::lean_inc(v_val_8404_);
                        leanh::lean_dec_ref_known(v_e_x3f_8403_, 1);
                        v___y_8395_ = v_val_8404_;
                        state = 1;
                        continue;
                    }
                }
            },
            1 => {
                v_toPure_8396_ = leanh::lean_ctor_get(v_toApplicative_8380_, 1);
                leanh::lean_inc(v_toPure_8396_);
                leanh::lean_dec_ref(v_toApplicative_8380_);
                v___x_8397_ = leanh::lean_apply_2(
                    v_toPure_8396_,
                    leanh::lean_box(0),
                    v___y_8395_,
                );
                return v___x_8397_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed(
    mut v_toApplicative_8405_: *mut leanh::LeanObject,
    mut v_inst_8406_: *mut leanh::LeanObject,
    mut v_inst_8407_: *mut leanh::LeanObject,
    mut v_inst_8408_: *mut leanh::LeanObject,
    mut v_pre_8409_: *mut leanh::LeanObject,
    mut v_post_8410_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8411_: *mut leanh::LeanObject,
    mut v_skipConstInApp_8412_: *mut leanh::LeanObject,
    mut v_skipInstances_8413_: *mut leanh::LeanObject,
    mut v_x_8414_: *mut leanh::LeanObject,
    mut v_x_8415_: *mut leanh::LeanObject,
    mut v_a_8416_: *mut leanh::LeanObject,
    mut v_e_8417_: *mut leanh::LeanObject,
    mut v_a_8418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_8419_: u8 = 0;
    let mut v_skipConstInApp_boxed_8420_: u8 = 0;
    let mut v_skipInstances_boxed_8421_: u8 = 0;
    let mut v_res_8422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_8419_ = (leanh::lean_unbox(v_usedLetOnly_8411_) as u8);
    v_skipConstInApp_boxed_8420_ = (leanh::lean_unbox(v_skipConstInApp_8412_) as u8);
    v_skipInstances_boxed_8421_ = (leanh::lean_unbox(v_skipInstances_8413_) as u8);
    v_res_8422_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(v_toApplicative_8405_, v_inst_8406_, v_inst_8407_, v_inst_8408_, v_pre_8409_, v_post_8410_, v_usedLetOnly_boxed_8419_, v_skipConstInApp_boxed_8420_, v_skipInstances_boxed_8421_, v_x_8414_, v_x_8415_, v_a_8416_, v_e_8417_, v_a_8418_);
    leanh::lean_dec(v_a_8416_);
    return v_res_8422_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(
    mut v_inst_8423_: *mut leanh::LeanObject,
    mut v_inst_8424_: *mut leanh::LeanObject,
    mut v_inst_8425_: *mut leanh::LeanObject,
    mut v_pre_8426_: *mut leanh::LeanObject,
    mut v_post_8427_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8428_: u8,
    mut v_skipConstInApp_8429_: u8,
    mut v_skipInstances_8430_: u8,
    mut v_x_8431_: *mut leanh::LeanObject,
    mut v_x_8432_: *mut leanh::LeanObject,
    mut v_e_8433_: *mut leanh::LeanObject,
    mut v_a_8434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_8435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_8436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_8435_ = leanh::lean_ctor_get(v_inst_8423_, 0);
    leanh::lean_inc_ref(v_toApplicative_8435_);
    v_toBind_8436_ = leanh::lean_ctor_get(v_inst_8423_, 1);
    leanh::lean_inc(v_toBind_8436_);
    v___x_8437_ = leanh::lean_box((v_usedLetOnly_8428_) as usize);
    v___x_8438_ = leanh::lean_box((v_skipConstInApp_8429_) as usize);
    v___x_8439_ = leanh::lean_box((v_skipInstances_8430_) as usize);
    leanh::lean_inc_ref(v_e_8433_);
    leanh::lean_inc(v_a_8434_);
    leanh::lean_inc(v_post_8427_);
    v___f_8440_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 13);
    leanh::lean_closure_set(v___f_8440_, 0, v_toApplicative_8435_);
    leanh::lean_closure_set(v___f_8440_, 1, v_inst_8423_);
    leanh::lean_closure_set(v___f_8440_, 2, v_inst_8424_);
    leanh::lean_closure_set(v___f_8440_, 3, v_inst_8425_);
    leanh::lean_closure_set(v___f_8440_, 4, v_pre_8426_);
    leanh::lean_closure_set(v___f_8440_, 5, v_post_8427_);
    leanh::lean_closure_set(v___f_8440_, 6, v___x_8437_);
    leanh::lean_closure_set(v___f_8440_, 7, v___x_8438_);
    leanh::lean_closure_set(v___f_8440_, 8, v___x_8439_);
    leanh::lean_closure_set(v___f_8440_, 9, v_x_8431_);
    leanh::lean_closure_set(v___f_8440_, 10, v_x_8432_);
    leanh::lean_closure_set(v___f_8440_, 11, v_a_8434_);
    leanh::lean_closure_set(v___f_8440_, 12, v_e_8433_);
    v___x_8441_ = leanh::lean_apply_1(v_post_8427_, v_e_8433_);
    v___x_8442_ = leanh::lean_apply_4(
        v_toBind_8436_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_8441_,
        v___f_8440_,
    );
    return v___x_8442_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(
    mut v_inst_8443_: *mut leanh::LeanObject,
    mut v_inst_8444_: *mut leanh::LeanObject,
    mut v_inst_8445_: *mut leanh::LeanObject,
    mut v_pre_8446_: *mut leanh::LeanObject,
    mut v_post_8447_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8448_: u8,
    mut v_skipConstInApp_8449_: u8,
    mut v_skipInstances_8450_: u8,
    mut v_x_8451_: *mut leanh::LeanObject,
    mut v_x_8452_: *mut leanh::LeanObject,
    mut v_a_8453_: *mut leanh::LeanObject,
    mut v_a_8454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8455_ =
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(
            v_inst_8443_,
            v_inst_8444_,
            v_inst_8445_,
            v_pre_8446_,
            v_post_8447_,
            v_usedLetOnly_8448_,
            v_skipConstInApp_8449_,
            v_skipInstances_8450_,
            v_x_8451_,
            v_x_8452_,
            v_a_8454_,
            v_a_8453_,
        );
    return v___x_8455_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___boxed(
    mut v_inst_8456_: *mut leanh::LeanObject,
    mut v_inst_8457_: *mut leanh::LeanObject,
    mut v_inst_8458_: *mut leanh::LeanObject,
    mut v_pre_8459_: *mut leanh::LeanObject,
    mut v_post_8460_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8461_: *mut leanh::LeanObject,
    mut v_skipConstInApp_8462_: *mut leanh::LeanObject,
    mut v_skipInstances_8463_: *mut leanh::LeanObject,
    mut v_x_8464_: *mut leanh::LeanObject,
    mut v_x_8465_: *mut leanh::LeanObject,
    mut v_e_8466_: *mut leanh::LeanObject,
    mut v_a_8467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_8468_: u8 = 0;
    let mut v_skipConstInApp_boxed_8469_: u8 = 0;
    let mut v_skipInstances_boxed_8470_: u8 = 0;
    let mut v_res_8471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_8468_ = (leanh::lean_unbox(v_usedLetOnly_8461_) as u8);
    v_skipConstInApp_boxed_8469_ = (leanh::lean_unbox(v_skipConstInApp_8462_) as u8);
    v_skipInstances_boxed_8470_ = (leanh::lean_unbox(v_skipInstances_8463_) as u8);
    v_res_8471_ =
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(
            v_inst_8456_,
            v_inst_8457_,
            v_inst_8458_,
            v_pre_8459_,
            v_post_8460_,
            v_usedLetOnly_boxed_8468_,
            v_skipConstInApp_boxed_8469_,
            v_skipInstances_boxed_8470_,
            v_x_8464_,
            v_x_8465_,
            v_e_8466_,
            v_a_8467_,
        );
    leanh::lean_dec(v_a_8467_);
    return v_res_8471_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___boxed(
    mut v_inst_8472_: *mut leanh::LeanObject,
    mut v_inst_8473_: *mut leanh::LeanObject,
    mut v_inst_8474_: *mut leanh::LeanObject,
    mut v_pre_8475_: *mut leanh::LeanObject,
    mut v_post_8476_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8477_: *mut leanh::LeanObject,
    mut v_skipConstInApp_8478_: *mut leanh::LeanObject,
    mut v_skipInstances_8479_: *mut leanh::LeanObject,
    mut v_x_8480_: *mut leanh::LeanObject,
    mut v_x_8481_: *mut leanh::LeanObject,
    mut v_fvars_8482_: *mut leanh::LeanObject,
    mut v_e_8483_: *mut leanh::LeanObject,
    mut v_a_8484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_8485_: u8 = 0;
    let mut v_skipConstInApp_boxed_8486_: u8 = 0;
    let mut v_skipInstances_boxed_8487_: u8 = 0;
    let mut v_res_8488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_8485_ = (leanh::lean_unbox(v_usedLetOnly_8477_) as u8);
    v_skipConstInApp_boxed_8486_ = (leanh::lean_unbox(v_skipConstInApp_8478_) as u8);
    v_skipInstances_boxed_8487_ = (leanh::lean_unbox(v_skipInstances_8479_) as u8);
    v_res_8488_ =
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(
            v_inst_8472_,
            v_inst_8473_,
            v_inst_8474_,
            v_pre_8475_,
            v_post_8476_,
            v_usedLetOnly_boxed_8485_,
            v_skipConstInApp_boxed_8486_,
            v_skipInstances_boxed_8487_,
            v_x_8480_,
            v_x_8481_,
            v_fvars_8482_,
            v_e_8483_,
            v_a_8484_,
        );
    leanh::lean_dec(v_a_8484_);
    return v_res_8488_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___boxed(
    mut v_inst_8489_: *mut leanh::LeanObject,
    mut v_inst_8490_: *mut leanh::LeanObject,
    mut v_inst_8491_: *mut leanh::LeanObject,
    mut v_pre_8492_: *mut leanh::LeanObject,
    mut v_post_8493_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8494_: *mut leanh::LeanObject,
    mut v_skipConstInApp_8495_: *mut leanh::LeanObject,
    mut v_skipInstances_8496_: *mut leanh::LeanObject,
    mut v_x_8497_: *mut leanh::LeanObject,
    mut v_x_8498_: *mut leanh::LeanObject,
    mut v_fvars_8499_: *mut leanh::LeanObject,
    mut v_e_8500_: *mut leanh::LeanObject,
    mut v_a_8501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_8502_: u8 = 0;
    let mut v_skipConstInApp_boxed_8503_: u8 = 0;
    let mut v_skipInstances_boxed_8504_: u8 = 0;
    let mut v_res_8505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_8502_ = (leanh::lean_unbox(v_usedLetOnly_8494_) as u8);
    v_skipConstInApp_boxed_8503_ = (leanh::lean_unbox(v_skipConstInApp_8495_) as u8);
    v_skipInstances_boxed_8504_ = (leanh::lean_unbox(v_skipInstances_8496_) as u8);
    v_res_8505_ =
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(
            v_inst_8489_,
            v_inst_8490_,
            v_inst_8491_,
            v_pre_8492_,
            v_post_8493_,
            v_usedLetOnly_boxed_8502_,
            v_skipConstInApp_boxed_8503_,
            v_skipInstances_boxed_8504_,
            v_x_8497_,
            v_x_8498_,
            v_fvars_8499_,
            v_e_8500_,
            v_a_8501_,
        );
    leanh::lean_dec(v_a_8501_);
    return v_res_8505_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___boxed(
    mut v_inst_8506_: *mut leanh::LeanObject,
    mut v_inst_8507_: *mut leanh::LeanObject,
    mut v_inst_8508_: *mut leanh::LeanObject,
    mut v_pre_8509_: *mut leanh::LeanObject,
    mut v_post_8510_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8511_: *mut leanh::LeanObject,
    mut v_skipConstInApp_8512_: *mut leanh::LeanObject,
    mut v_skipInstances_8513_: *mut leanh::LeanObject,
    mut v_x_8514_: *mut leanh::LeanObject,
    mut v_x_8515_: *mut leanh::LeanObject,
    mut v_fvars_8516_: *mut leanh::LeanObject,
    mut v_e_8517_: *mut leanh::LeanObject,
    mut v_a_8518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_8519_: u8 = 0;
    let mut v_skipConstInApp_boxed_8520_: u8 = 0;
    let mut v_skipInstances_boxed_8521_: u8 = 0;
    let mut v_res_8522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_8519_ = (leanh::lean_unbox(v_usedLetOnly_8511_) as u8);
    v_skipConstInApp_boxed_8520_ = (leanh::lean_unbox(v_skipConstInApp_8512_) as u8);
    v_skipInstances_boxed_8521_ = (leanh::lean_unbox(v_skipInstances_8513_) as u8);
    v_res_8522_ =
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(
            v_inst_8506_,
            v_inst_8507_,
            v_inst_8508_,
            v_pre_8509_,
            v_post_8510_,
            v_usedLetOnly_boxed_8519_,
            v_skipConstInApp_boxed_8520_,
            v_skipInstances_boxed_8521_,
            v_x_8514_,
            v_x_8515_,
            v_fvars_8516_,
            v_e_8517_,
            v_a_8518_,
        );
    leanh::lean_dec(v_a_8518_);
    return v_res_8522_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(
    mut v_m_8523_: *mut leanh::LeanObject,
    mut v_inst_8524_: *mut leanh::LeanObject,
    mut v_inst_8525_: *mut leanh::LeanObject,
    mut v_inst_8526_: *mut leanh::LeanObject,
    mut v_pre_8527_: *mut leanh::LeanObject,
    mut v_post_8528_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8529_: u8,
    mut v_skipConstInApp_8530_: u8,
    mut v_skipInstances_8531_: u8,
    mut v_x_8532_: *mut leanh::LeanObject,
    mut v_x_8533_: *mut leanh::LeanObject,
    mut v_e_8534_: *mut leanh::LeanObject,
    mut v_a_8535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8536_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(
        v_inst_8524_,
        v_inst_8525_,
        v_inst_8526_,
        v_pre_8527_,
        v_post_8528_,
        v_usedLetOnly_8529_,
        v_skipConstInApp_8530_,
        v_skipInstances_8531_,
        v_x_8532_,
        v_x_8533_,
        v_e_8534_,
        v_a_8535_,
    );
    return v___x_8536_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___boxed(
    mut v_m_8537_: *mut leanh::LeanObject,
    mut v_inst_8538_: *mut leanh::LeanObject,
    mut v_inst_8539_: *mut leanh::LeanObject,
    mut v_inst_8540_: *mut leanh::LeanObject,
    mut v_pre_8541_: *mut leanh::LeanObject,
    mut v_post_8542_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8543_: *mut leanh::LeanObject,
    mut v_skipConstInApp_8544_: *mut leanh::LeanObject,
    mut v_skipInstances_8545_: *mut leanh::LeanObject,
    mut v_x_8546_: *mut leanh::LeanObject,
    mut v_x_8547_: *mut leanh::LeanObject,
    mut v_e_8548_: *mut leanh::LeanObject,
    mut v_a_8549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_8550_: u8 = 0;
    let mut v_skipConstInApp_boxed_8551_: u8 = 0;
    let mut v_skipInstances_boxed_8552_: u8 = 0;
    let mut v_res_8553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_8550_ = (leanh::lean_unbox(v_usedLetOnly_8543_) as u8);
    v_skipConstInApp_boxed_8551_ = (leanh::lean_unbox(v_skipConstInApp_8544_) as u8);
    v_skipInstances_boxed_8552_ = (leanh::lean_unbox(v_skipInstances_8545_) as u8);
    v_res_8553_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(
        v_m_8537_,
        v_inst_8538_,
        v_inst_8539_,
        v_inst_8540_,
        v_pre_8541_,
        v_post_8542_,
        v_usedLetOnly_boxed_8550_,
        v_skipConstInApp_boxed_8551_,
        v_skipInstances_boxed_8552_,
        v_x_8546_,
        v_x_8547_,
        v_e_8548_,
        v_a_8549_,
    );
    leanh::lean_dec(v_a_8549_);
    return v_res_8553_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(
    mut v_m_8554_: *mut leanh::LeanObject,
    mut v_inst_8555_: *mut leanh::LeanObject,
    mut v_inst_8556_: *mut leanh::LeanObject,
    mut v_inst_8557_: *mut leanh::LeanObject,
    mut v_pre_8558_: *mut leanh::LeanObject,
    mut v_post_8559_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8560_: u8,
    mut v_skipConstInApp_8561_: u8,
    mut v_skipInstances_8562_: u8,
    mut v_x_8563_: *mut leanh::LeanObject,
    mut v_x_8564_: *mut leanh::LeanObject,
    mut v_fvars_8565_: *mut leanh::LeanObject,
    mut v_e_8566_: *mut leanh::LeanObject,
    mut v_a_8567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8568_ =
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(
            v_inst_8555_,
            v_inst_8556_,
            v_inst_8557_,
            v_pre_8558_,
            v_post_8559_,
            v_usedLetOnly_8560_,
            v_skipConstInApp_8561_,
            v_skipInstances_8562_,
            v_x_8563_,
            v_x_8564_,
            v_fvars_8565_,
            v_e_8566_,
            v_a_8567_,
        );
    return v___x_8568_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___boxed(
    mut v_m_8569_: *mut leanh::LeanObject,
    mut v_inst_8570_: *mut leanh::LeanObject,
    mut v_inst_8571_: *mut leanh::LeanObject,
    mut v_inst_8572_: *mut leanh::LeanObject,
    mut v_pre_8573_: *mut leanh::LeanObject,
    mut v_post_8574_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8575_: *mut leanh::LeanObject,
    mut v_skipConstInApp_8576_: *mut leanh::LeanObject,
    mut v_skipInstances_8577_: *mut leanh::LeanObject,
    mut v_x_8578_: *mut leanh::LeanObject,
    mut v_x_8579_: *mut leanh::LeanObject,
    mut v_fvars_8580_: *mut leanh::LeanObject,
    mut v_e_8581_: *mut leanh::LeanObject,
    mut v_a_8582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_8583_: u8 = 0;
    let mut v_skipConstInApp_boxed_8584_: u8 = 0;
    let mut v_skipInstances_boxed_8585_: u8 = 0;
    let mut v_res_8586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_8583_ = (leanh::lean_unbox(v_usedLetOnly_8575_) as u8);
    v_skipConstInApp_boxed_8584_ = (leanh::lean_unbox(v_skipConstInApp_8576_) as u8);
    v_skipInstances_boxed_8585_ = (leanh::lean_unbox(v_skipInstances_8577_) as u8);
    v_res_8586_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(
        v_m_8569_,
        v_inst_8570_,
        v_inst_8571_,
        v_inst_8572_,
        v_pre_8573_,
        v_post_8574_,
        v_usedLetOnly_boxed_8583_,
        v_skipConstInApp_boxed_8584_,
        v_skipInstances_boxed_8585_,
        v_x_8578_,
        v_x_8579_,
        v_fvars_8580_,
        v_e_8581_,
        v_a_8582_,
    );
    leanh::lean_dec(v_a_8582_);
    return v_res_8586_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(
    mut v_m_8587_: *mut leanh::LeanObject,
    mut v_inst_8588_: *mut leanh::LeanObject,
    mut v_inst_8589_: *mut leanh::LeanObject,
    mut v_inst_8590_: *mut leanh::LeanObject,
    mut v_pre_8591_: *mut leanh::LeanObject,
    mut v_post_8592_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8593_: u8,
    mut v_skipConstInApp_8594_: u8,
    mut v_skipInstances_8595_: u8,
    mut v_x_8596_: *mut leanh::LeanObject,
    mut v_x_8597_: *mut leanh::LeanObject,
    mut v_e_8598_: *mut leanh::LeanObject,
    mut v_a_8599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8600_ =
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(
            v_inst_8588_,
            v_inst_8589_,
            v_inst_8590_,
            v_pre_8591_,
            v_post_8592_,
            v_usedLetOnly_8593_,
            v_skipConstInApp_8594_,
            v_skipInstances_8595_,
            v_x_8596_,
            v_x_8597_,
            v_e_8598_,
            v_a_8599_,
        );
    return v___x_8600_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___boxed(
    mut v_m_8601_: *mut leanh::LeanObject,
    mut v_inst_8602_: *mut leanh::LeanObject,
    mut v_inst_8603_: *mut leanh::LeanObject,
    mut v_inst_8604_: *mut leanh::LeanObject,
    mut v_pre_8605_: *mut leanh::LeanObject,
    mut v_post_8606_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8607_: *mut leanh::LeanObject,
    mut v_skipConstInApp_8608_: *mut leanh::LeanObject,
    mut v_skipInstances_8609_: *mut leanh::LeanObject,
    mut v_x_8610_: *mut leanh::LeanObject,
    mut v_x_8611_: *mut leanh::LeanObject,
    mut v_e_8612_: *mut leanh::LeanObject,
    mut v_a_8613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_8614_: u8 = 0;
    let mut v_skipConstInApp_boxed_8615_: u8 = 0;
    let mut v_skipInstances_boxed_8616_: u8 = 0;
    let mut v_res_8617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_8614_ = (leanh::lean_unbox(v_usedLetOnly_8607_) as u8);
    v_skipConstInApp_boxed_8615_ = (leanh::lean_unbox(v_skipConstInApp_8608_) as u8);
    v_skipInstances_boxed_8616_ = (leanh::lean_unbox(v_skipInstances_8609_) as u8);
    v_res_8617_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(
        v_m_8601_,
        v_inst_8602_,
        v_inst_8603_,
        v_inst_8604_,
        v_pre_8605_,
        v_post_8606_,
        v_usedLetOnly_boxed_8614_,
        v_skipConstInApp_boxed_8615_,
        v_skipInstances_boxed_8616_,
        v_x_8610_,
        v_x_8611_,
        v_e_8612_,
        v_a_8613_,
    );
    leanh::lean_dec(v_a_8613_);
    return v_res_8617_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(
    mut v_m_8618_: *mut leanh::LeanObject,
    mut v_inst_8619_: *mut leanh::LeanObject,
    mut v_inst_8620_: *mut leanh::LeanObject,
    mut v_inst_8621_: *mut leanh::LeanObject,
    mut v_pre_8622_: *mut leanh::LeanObject,
    mut v_post_8623_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8624_: u8,
    mut v_skipConstInApp_8625_: u8,
    mut v_skipInstances_8626_: u8,
    mut v_x_8627_: *mut leanh::LeanObject,
    mut v_x_8628_: *mut leanh::LeanObject,
    mut v_fvars_8629_: *mut leanh::LeanObject,
    mut v_e_8630_: *mut leanh::LeanObject,
    mut v_a_8631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8632_ =
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(
            v_inst_8619_,
            v_inst_8620_,
            v_inst_8621_,
            v_pre_8622_,
            v_post_8623_,
            v_usedLetOnly_8624_,
            v_skipConstInApp_8625_,
            v_skipInstances_8626_,
            v_x_8627_,
            v_x_8628_,
            v_fvars_8629_,
            v_e_8630_,
            v_a_8631_,
        );
    return v___x_8632_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___boxed(
    mut v_m_8633_: *mut leanh::LeanObject,
    mut v_inst_8634_: *mut leanh::LeanObject,
    mut v_inst_8635_: *mut leanh::LeanObject,
    mut v_inst_8636_: *mut leanh::LeanObject,
    mut v_pre_8637_: *mut leanh::LeanObject,
    mut v_post_8638_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8639_: *mut leanh::LeanObject,
    mut v_skipConstInApp_8640_: *mut leanh::LeanObject,
    mut v_skipInstances_8641_: *mut leanh::LeanObject,
    mut v_x_8642_: *mut leanh::LeanObject,
    mut v_x_8643_: *mut leanh::LeanObject,
    mut v_fvars_8644_: *mut leanh::LeanObject,
    mut v_e_8645_: *mut leanh::LeanObject,
    mut v_a_8646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_8647_: u8 = 0;
    let mut v_skipConstInApp_boxed_8648_: u8 = 0;
    let mut v_skipInstances_boxed_8649_: u8 = 0;
    let mut v_res_8650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_8647_ = (leanh::lean_unbox(v_usedLetOnly_8639_) as u8);
    v_skipConstInApp_boxed_8648_ = (leanh::lean_unbox(v_skipConstInApp_8640_) as u8);
    v_skipInstances_boxed_8649_ = (leanh::lean_unbox(v_skipInstances_8641_) as u8);
    v_res_8650_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(
        v_m_8633_,
        v_inst_8634_,
        v_inst_8635_,
        v_inst_8636_,
        v_pre_8637_,
        v_post_8638_,
        v_usedLetOnly_boxed_8647_,
        v_skipConstInApp_boxed_8648_,
        v_skipInstances_boxed_8649_,
        v_x_8642_,
        v_x_8643_,
        v_fvars_8644_,
        v_e_8645_,
        v_a_8646_,
    );
    leanh::lean_dec(v_a_8646_);
    return v_res_8650_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(
    mut v_m_8651_: *mut leanh::LeanObject,
    mut v_inst_8652_: *mut leanh::LeanObject,
    mut v_inst_8653_: *mut leanh::LeanObject,
    mut v_inst_8654_: *mut leanh::LeanObject,
    mut v_pre_8655_: *mut leanh::LeanObject,
    mut v_post_8656_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8657_: u8,
    mut v_skipConstInApp_8658_: u8,
    mut v_skipInstances_8659_: u8,
    mut v_x_8660_: *mut leanh::LeanObject,
    mut v_x_8661_: *mut leanh::LeanObject,
    mut v_fvars_8662_: *mut leanh::LeanObject,
    mut v_e_8663_: *mut leanh::LeanObject,
    mut v_a_8664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8665_ =
        l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(
            v_inst_8652_,
            v_inst_8653_,
            v_inst_8654_,
            v_pre_8655_,
            v_post_8656_,
            v_usedLetOnly_8657_,
            v_skipConstInApp_8658_,
            v_skipInstances_8659_,
            v_x_8660_,
            v_x_8661_,
            v_fvars_8662_,
            v_e_8663_,
            v_a_8664_,
        );
    return v___x_8665_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___boxed(
    mut v_m_8666_: *mut leanh::LeanObject,
    mut v_inst_8667_: *mut leanh::LeanObject,
    mut v_inst_8668_: *mut leanh::LeanObject,
    mut v_inst_8669_: *mut leanh::LeanObject,
    mut v_pre_8670_: *mut leanh::LeanObject,
    mut v_post_8671_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8672_: *mut leanh::LeanObject,
    mut v_skipConstInApp_8673_: *mut leanh::LeanObject,
    mut v_skipInstances_8674_: *mut leanh::LeanObject,
    mut v_x_8675_: *mut leanh::LeanObject,
    mut v_x_8676_: *mut leanh::LeanObject,
    mut v_fvars_8677_: *mut leanh::LeanObject,
    mut v_e_8678_: *mut leanh::LeanObject,
    mut v_a_8679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_8680_: u8 = 0;
    let mut v_skipConstInApp_boxed_8681_: u8 = 0;
    let mut v_skipInstances_boxed_8682_: u8 = 0;
    let mut v_res_8683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_8680_ = (leanh::lean_unbox(v_usedLetOnly_8672_) as u8);
    v_skipConstInApp_boxed_8681_ = (leanh::lean_unbox(v_skipConstInApp_8673_) as u8);
    v_skipInstances_boxed_8682_ = (leanh::lean_unbox(v_skipInstances_8674_) as u8);
    v_res_8683_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(
        v_m_8666_,
        v_inst_8667_,
        v_inst_8668_,
        v_inst_8669_,
        v_pre_8670_,
        v_post_8671_,
        v_usedLetOnly_boxed_8680_,
        v_skipConstInApp_boxed_8681_,
        v_skipInstances_boxed_8682_,
        v_x_8675_,
        v_x_8676_,
        v_fvars_8677_,
        v_e_8678_,
        v_a_8679_,
    );
    leanh::lean_dec(v_a_8679_);
    return v_res_8683_;
}
pub unsafe fn l_Lean_Meta_transformWithCache___redArg___lam__0(
    mut v_x_8684_: *mut leanh::LeanObject,
    mut v___y_8685_: *mut leanh::LeanObject,
    mut v___y_8686_: *mut leanh::LeanObject,
    mut v___y_8687_: *mut leanh::LeanObject,
    mut v___y_8688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8690_ = leanh::lean_apply_1(v_x_8684_, leanh::lean_box(0));
    v___x_8691_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_8691_, 0, v___x_8690_);
    return v___x_8691_;
}
pub unsafe fn l_Lean_Meta_transformWithCache___redArg___lam__0___boxed(
    mut v_x_8692_: *mut leanh::LeanObject,
    mut v___y_8693_: *mut leanh::LeanObject,
    mut v___y_8694_: *mut leanh::LeanObject,
    mut v___y_8695_: *mut leanh::LeanObject,
    mut v___y_8696_: *mut leanh::LeanObject,
    mut v___y_8697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8698_ = l_Lean_Meta_transformWithCache___redArg___lam__0(
        v_x_8692_,
        v___y_8693_,
        v___y_8694_,
        v___y_8695_,
        v___y_8696_,
    );
    leanh::lean_dec(v___y_8696_);
    leanh::lean_dec_ref(v___y_8695_);
    leanh::lean_dec(v___y_8694_);
    leanh::lean_dec_ref(v___y_8693_);
    return v_res_8698_;
}
pub unsafe fn l_Lean_Meta_transformWithCache___redArg___lam__1(
    mut v_inst_8699_: *mut leanh::LeanObject,
    mut v_00_u03b1_8700_: *mut leanh::LeanObject,
    mut v_x_8701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_8702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_8702_ = leanh::lean_alloc_closure(
        l_Lean_Meta_transformWithCache___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_8702_, 0, v_x_8701_);
    v___x_8703_ = leanh::lean_apply_2(v_inst_8699_, leanh::lean_box(0), v___f_8702_);
    return v___x_8703_;
}
pub unsafe fn l_Lean_Meta_transformWithCache___redArg___lam__4(
    mut v_toPure_8704_: *mut leanh::LeanObject,
    mut v_x_8705_: *mut leanh::LeanObject,
    mut v_toBind_8706_: *mut leanh::LeanObject,
    mut v_inst_8707_: *mut leanh::LeanObject,
    mut v_inst_8708_: *mut leanh::LeanObject,
    mut v_inst_8709_: *mut leanh::LeanObject,
    mut v_pre_8710_: *mut leanh::LeanObject,
    mut v_post_8711_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8712_: u8,
    mut v_skipConstInApp_8713_: u8,
    mut v_skipInstances_8714_: u8,
    mut v_x_8715_: *mut leanh::LeanObject,
    mut v_input_8716_: *mut leanh::LeanObject,
    mut v_ref_8717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_8718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8720_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_8706_);
    leanh::lean_inc(v_x_8705_);
    leanh::lean_inc(v_ref_8717_);
    v___f_8718_ = leanh::lean_alloc_closure(
        l_Lean_Core_transform___redArg___lam__4 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_8718_, 0, v_toPure_8704_);
    leanh::lean_closure_set(v___f_8718_, 1, v_ref_8717_);
    leanh::lean_closure_set(v___f_8718_, 2, v_x_8705_);
    leanh::lean_closure_set(v___f_8718_, 3, v_toBind_8706_);
    v___x_8719_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(
        v_inst_8707_,
        v_inst_8708_,
        v_inst_8709_,
        v_pre_8710_,
        v_post_8711_,
        v_usedLetOnly_8712_,
        v_skipConstInApp_8713_,
        v_skipInstances_8714_,
        v_x_8715_,
        v_x_8705_,
        v_input_8716_,
        v_ref_8717_,
    );
    leanh::lean_dec(v_ref_8717_);
    v___x_8720_ = leanh::lean_apply_4(
        v_toBind_8706_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_8719_,
        v___f_8718_,
    );
    return v___x_8720_;
}
pub unsafe fn l_Lean_Meta_transformWithCache___redArg___lam__4___boxed(
    mut v_toPure_8721_: *mut leanh::LeanObject,
    mut v_x_8722_: *mut leanh::LeanObject,
    mut v_toBind_8723_: *mut leanh::LeanObject,
    mut v_inst_8724_: *mut leanh::LeanObject,
    mut v_inst_8725_: *mut leanh::LeanObject,
    mut v_inst_8726_: *mut leanh::LeanObject,
    mut v_pre_8727_: *mut leanh::LeanObject,
    mut v_post_8728_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8729_: *mut leanh::LeanObject,
    mut v_skipConstInApp_8730_: *mut leanh::LeanObject,
    mut v_skipInstances_8731_: *mut leanh::LeanObject,
    mut v_x_8732_: *mut leanh::LeanObject,
    mut v_input_8733_: *mut leanh::LeanObject,
    mut v_ref_8734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_8735_: u8 = 0;
    let mut v_skipConstInApp_boxed_8736_: u8 = 0;
    let mut v_skipInstances_boxed_8737_: u8 = 0;
    let mut v_res_8738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_8735_ = (leanh::lean_unbox(v_usedLetOnly_8729_) as u8);
    v_skipConstInApp_boxed_8736_ = (leanh::lean_unbox(v_skipConstInApp_8730_) as u8);
    v_skipInstances_boxed_8737_ = (leanh::lean_unbox(v_skipInstances_8731_) as u8);
    v_res_8738_ = l_Lean_Meta_transformWithCache___redArg___lam__4(
        v_toPure_8721_,
        v_x_8722_,
        v_toBind_8723_,
        v_inst_8724_,
        v_inst_8725_,
        v_inst_8726_,
        v_pre_8727_,
        v_post_8728_,
        v_usedLetOnly_boxed_8735_,
        v_skipConstInApp_boxed_8736_,
        v_skipInstances_boxed_8737_,
        v_x_8732_,
        v_input_8733_,
        v_ref_8734_,
    );
    return v_res_8738_;
}
pub unsafe fn l_Lean_Meta_transformWithCache___redArg(
    mut v_inst_8739_: *mut leanh::LeanObject,
    mut v_inst_8740_: *mut leanh::LeanObject,
    mut v_inst_8741_: *mut leanh::LeanObject,
    mut v_input_8742_: *mut leanh::LeanObject,
    mut v_cache_8743_: *mut leanh::LeanObject,
    mut v_pre_8744_: *mut leanh::LeanObject,
    mut v_post_8745_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8746_: u8,
    mut v_skipConstInApp_8747_: u8,
    mut v_skipInstances_8748_: u8,
) -> *mut leanh::LeanObject {
    let mut v_x_8749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_8750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_8751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_8752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_8753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8760_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_8749_ = leanh::lean_box(0);
    v_toApplicative_8750_ = leanh::lean_ctor_get(v_inst_8739_, 0);
    v_toBind_8751_ = leanh::lean_ctor_get(v_inst_8739_, 1);
    leanh::lean_inc_n(v_toBind_8751_, 2);
    v_toPure_8752_ = leanh::lean_ctor_get(v_toApplicative_8750_, 1);
    leanh::lean_inc(v_toPure_8752_);
    leanh::lean_inc_n(v_inst_8740_, 2);
    v_x_8753_ = leanh::lean_alloc_closure(
        l_Lean_Meta_transformWithCache___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v_x_8753_, 0, v_inst_8740_);
    v___x_8754_ =
        leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_8754_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_8754_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_8754_, 2, v_cache_8743_);
    v___x_8755_ = l_Lean_Meta_transformWithCache___redArg___lam__1(
        v_inst_8740_,
        leanh::lean_box(0),
        v___x_8754_,
    );
    v___x_8756_ = leanh::lean_box((v_usedLetOnly_8746_) as usize);
    v___x_8757_ = leanh::lean_box((v_skipConstInApp_8747_) as usize);
    v___x_8758_ = leanh::lean_box((v_skipInstances_8748_) as usize);
    v___f_8759_ = leanh::lean_alloc_closure(
        l_Lean_Meta_transformWithCache___redArg___lam__4___boxed as *mut core::ffi::c_void,
        14,
        13,
    );
    leanh::lean_closure_set(v___f_8759_, 0, v_toPure_8752_);
    leanh::lean_closure_set(v___f_8759_, 1, v_x_8753_);
    leanh::lean_closure_set(v___f_8759_, 2, v_toBind_8751_);
    leanh::lean_closure_set(v___f_8759_, 3, v_inst_8739_);
    leanh::lean_closure_set(v___f_8759_, 4, v_inst_8740_);
    leanh::lean_closure_set(v___f_8759_, 5, v_inst_8741_);
    leanh::lean_closure_set(v___f_8759_, 6, v_pre_8744_);
    leanh::lean_closure_set(v___f_8759_, 7, v_post_8745_);
    leanh::lean_closure_set(v___f_8759_, 8, v___x_8756_);
    leanh::lean_closure_set(v___f_8759_, 9, v___x_8757_);
    leanh::lean_closure_set(v___f_8759_, 10, v___x_8758_);
    leanh::lean_closure_set(v___f_8759_, 11, v_x_8749_);
    leanh::lean_closure_set(v___f_8759_, 12, v_input_8742_);
    v___x_8760_ = leanh::lean_apply_4(
        v_toBind_8751_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_8755_,
        v___f_8759_,
    );
    return v___x_8760_;
}
pub unsafe fn l_Lean_Meta_transformWithCache___redArg___boxed(
    mut v_inst_8761_: *mut leanh::LeanObject,
    mut v_inst_8762_: *mut leanh::LeanObject,
    mut v_inst_8763_: *mut leanh::LeanObject,
    mut v_input_8764_: *mut leanh::LeanObject,
    mut v_cache_8765_: *mut leanh::LeanObject,
    mut v_pre_8766_: *mut leanh::LeanObject,
    mut v_post_8767_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8768_: *mut leanh::LeanObject,
    mut v_skipConstInApp_8769_: *mut leanh::LeanObject,
    mut v_skipInstances_8770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_8771_: u8 = 0;
    let mut v_skipConstInApp_boxed_8772_: u8 = 0;
    let mut v_skipInstances_boxed_8773_: u8 = 0;
    let mut v_res_8774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_8771_ = (leanh::lean_unbox(v_usedLetOnly_8768_) as u8);
    v_skipConstInApp_boxed_8772_ = (leanh::lean_unbox(v_skipConstInApp_8769_) as u8);
    v_skipInstances_boxed_8773_ = (leanh::lean_unbox(v_skipInstances_8770_) as u8);
    v_res_8774_ = l_Lean_Meta_transformWithCache___redArg(
        v_inst_8761_,
        v_inst_8762_,
        v_inst_8763_,
        v_input_8764_,
        v_cache_8765_,
        v_pre_8766_,
        v_post_8767_,
        v_usedLetOnly_boxed_8771_,
        v_skipConstInApp_boxed_8772_,
        v_skipInstances_boxed_8773_,
    );
    return v_res_8774_;
}
pub unsafe fn l_Lean_Meta_transformWithCache(
    mut v_m_8775_: *mut leanh::LeanObject,
    mut v_inst_8776_: *mut leanh::LeanObject,
    mut v_inst_8777_: *mut leanh::LeanObject,
    mut v_inst_8778_: *mut leanh::LeanObject,
    mut v_input_8779_: *mut leanh::LeanObject,
    mut v_cache_8780_: *mut leanh::LeanObject,
    mut v_pre_8781_: *mut leanh::LeanObject,
    mut v_post_8782_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8783_: u8,
    mut v_skipConstInApp_8784_: u8,
    mut v_skipInstances_8785_: u8,
) -> *mut leanh::LeanObject {
    let mut v_x_8786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_8787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_8788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_8789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_8790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_8786_ = leanh::lean_box(0);
    v_toApplicative_8787_ = leanh::lean_ctor_get(v_inst_8776_, 0);
    v_toBind_8788_ = leanh::lean_ctor_get(v_inst_8776_, 1);
    leanh::lean_inc_n(v_toBind_8788_, 2);
    v_toPure_8789_ = leanh::lean_ctor_get(v_toApplicative_8787_, 1);
    leanh::lean_inc(v_toPure_8789_);
    leanh::lean_inc_n(v_inst_8777_, 2);
    v_x_8790_ = leanh::lean_alloc_closure(
        l_Lean_Meta_transformWithCache___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v_x_8790_, 0, v_inst_8777_);
    v___x_8791_ =
        leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_8791_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_8791_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_8791_, 2, v_cache_8780_);
    v___x_8792_ = l_Lean_Meta_transformWithCache___redArg___lam__1(
        v_inst_8777_,
        leanh::lean_box(0),
        v___x_8791_,
    );
    v___x_8793_ = leanh::lean_box((v_usedLetOnly_8783_) as usize);
    v___x_8794_ = leanh::lean_box((v_skipConstInApp_8784_) as usize);
    v___x_8795_ = leanh::lean_box((v_skipInstances_8785_) as usize);
    v___f_8796_ = leanh::lean_alloc_closure(
        l_Lean_Meta_transformWithCache___redArg___lam__4___boxed as *mut core::ffi::c_void,
        14,
        13,
    );
    leanh::lean_closure_set(v___f_8796_, 0, v_toPure_8789_);
    leanh::lean_closure_set(v___f_8796_, 1, v_x_8790_);
    leanh::lean_closure_set(v___f_8796_, 2, v_toBind_8788_);
    leanh::lean_closure_set(v___f_8796_, 3, v_inst_8776_);
    leanh::lean_closure_set(v___f_8796_, 4, v_inst_8777_);
    leanh::lean_closure_set(v___f_8796_, 5, v_inst_8778_);
    leanh::lean_closure_set(v___f_8796_, 6, v_pre_8781_);
    leanh::lean_closure_set(v___f_8796_, 7, v_post_8782_);
    leanh::lean_closure_set(v___f_8796_, 8, v___x_8793_);
    leanh::lean_closure_set(v___f_8796_, 9, v___x_8794_);
    leanh::lean_closure_set(v___f_8796_, 10, v___x_8795_);
    leanh::lean_closure_set(v___f_8796_, 11, v_x_8786_);
    leanh::lean_closure_set(v___f_8796_, 12, v_input_8779_);
    v___x_8797_ = leanh::lean_apply_4(
        v_toBind_8788_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_8792_,
        v___f_8796_,
    );
    return v___x_8797_;
}
pub unsafe fn l_Lean_Meta_transformWithCache___boxed(
    mut v_m_8798_: *mut leanh::LeanObject,
    mut v_inst_8799_: *mut leanh::LeanObject,
    mut v_inst_8800_: *mut leanh::LeanObject,
    mut v_inst_8801_: *mut leanh::LeanObject,
    mut v_input_8802_: *mut leanh::LeanObject,
    mut v_cache_8803_: *mut leanh::LeanObject,
    mut v_pre_8804_: *mut leanh::LeanObject,
    mut v_post_8805_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8806_: *mut leanh::LeanObject,
    mut v_skipConstInApp_8807_: *mut leanh::LeanObject,
    mut v_skipInstances_8808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_8809_: u8 = 0;
    let mut v_skipConstInApp_boxed_8810_: u8 = 0;
    let mut v_skipInstances_boxed_8811_: u8 = 0;
    let mut v_res_8812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_8809_ = (leanh::lean_unbox(v_usedLetOnly_8806_) as u8);
    v_skipConstInApp_boxed_8810_ = (leanh::lean_unbox(v_skipConstInApp_8807_) as u8);
    v_skipInstances_boxed_8811_ = (leanh::lean_unbox(v_skipInstances_8808_) as u8);
    v_res_8812_ = l_Lean_Meta_transformWithCache(
        v_m_8798_,
        v_inst_8799_,
        v_inst_8800_,
        v_inst_8801_,
        v_input_8802_,
        v_cache_8803_,
        v_pre_8804_,
        v_post_8805_,
        v_usedLetOnly_boxed_8809_,
        v_skipConstInApp_boxed_8810_,
        v_skipInstances_boxed_8811_,
    );
    return v_res_8812_;
}
pub unsafe fn l_Lean_Meta_transform___redArg___lam__5(
    mut v_toPure_8813_: *mut leanh::LeanObject,
    mut v_x_8814_: *mut leanh::LeanObject,
    mut v_toBind_8815_: *mut leanh::LeanObject,
    mut v_inst_8816_: *mut leanh::LeanObject,
    mut v_inst_8817_: *mut leanh::LeanObject,
    mut v_inst_8818_: *mut leanh::LeanObject,
    mut v_pre_8819_: *mut leanh::LeanObject,
    mut v_post_8820_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8821_: u8,
    mut v_skipConstInApp_8822_: u8,
    mut v___x_8823_: u8,
    mut v_x_8824_: *mut leanh::LeanObject,
    mut v_input_8825_: *mut leanh::LeanObject,
    mut v_ref_8826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_8827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8829_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_8815_);
    leanh::lean_inc(v_x_8814_);
    leanh::lean_inc(v_ref_8826_);
    v___f_8827_ = leanh::lean_alloc_closure(
        l_Lean_Core_transform___redArg___lam__4 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_8827_, 0, v_toPure_8813_);
    leanh::lean_closure_set(v___f_8827_, 1, v_ref_8826_);
    leanh::lean_closure_set(v___f_8827_, 2, v_x_8814_);
    leanh::lean_closure_set(v___f_8827_, 3, v_toBind_8815_);
    v___x_8828_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(
        v_inst_8816_,
        v_inst_8817_,
        v_inst_8818_,
        v_pre_8819_,
        v_post_8820_,
        v_usedLetOnly_8821_,
        v_skipConstInApp_8822_,
        v___x_8823_,
        v_x_8824_,
        v_x_8814_,
        v_input_8825_,
        v_ref_8826_,
    );
    leanh::lean_dec(v_ref_8826_);
    v___x_8829_ = leanh::lean_apply_4(
        v_toBind_8815_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_8828_,
        v___f_8827_,
    );
    return v___x_8829_;
}
pub unsafe fn l_Lean_Meta_transform___redArg___lam__5___boxed(
    mut v_toPure_8830_: *mut leanh::LeanObject,
    mut v_x_8831_: *mut leanh::LeanObject,
    mut v_toBind_8832_: *mut leanh::LeanObject,
    mut v_inst_8833_: *mut leanh::LeanObject,
    mut v_inst_8834_: *mut leanh::LeanObject,
    mut v_inst_8835_: *mut leanh::LeanObject,
    mut v_pre_8836_: *mut leanh::LeanObject,
    mut v_post_8837_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8838_: *mut leanh::LeanObject,
    mut v_skipConstInApp_8839_: *mut leanh::LeanObject,
    mut v___x_8840_: *mut leanh::LeanObject,
    mut v_x_8841_: *mut leanh::LeanObject,
    mut v_input_8842_: *mut leanh::LeanObject,
    mut v_ref_8843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_8844_: u8 = 0;
    let mut v_skipConstInApp_boxed_8845_: u8 = 0;
    let mut v___x_114__boxed_8846_: u8 = 0;
    let mut v_res_8847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_8844_ = (leanh::lean_unbox(v_usedLetOnly_8838_) as u8);
    v_skipConstInApp_boxed_8845_ = (leanh::lean_unbox(v_skipConstInApp_8839_) as u8);
    v___x_114__boxed_8846_ = (leanh::lean_unbox(v___x_8840_) as u8);
    v_res_8847_ = l_Lean_Meta_transform___redArg___lam__5(
        v_toPure_8830_,
        v_x_8831_,
        v_toBind_8832_,
        v_inst_8833_,
        v_inst_8834_,
        v_inst_8835_,
        v_pre_8836_,
        v_post_8837_,
        v_usedLetOnly_boxed_8844_,
        v_skipConstInApp_boxed_8845_,
        v___x_114__boxed_8846_,
        v_x_8841_,
        v_input_8842_,
        v_ref_8843_,
    );
    return v_res_8847_;
}
pub unsafe fn l_Lean_Meta_transform___redArg(
    mut v_inst_8848_: *mut leanh::LeanObject,
    mut v_inst_8849_: *mut leanh::LeanObject,
    mut v_inst_8850_: *mut leanh::LeanObject,
    mut v_input_8851_: *mut leanh::LeanObject,
    mut v_pre_8852_: *mut leanh::LeanObject,
    mut v_post_8853_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8854_: u8,
    mut v_skipConstInApp_8855_: u8,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_8856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_8857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_8858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_8859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_8860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8861_: u8 = 0;
    let mut v___x_8862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_8856_ = leanh::lean_ctor_get(v_inst_8848_, 0);
    v_toBind_8857_ = leanh::lean_ctor_get(v_inst_8848_, 1);
    leanh::lean_inc_n(v_toBind_8857_, 3);
    v_x_8858_ = leanh::lean_box(0);
    v_toPure_8859_ = leanh::lean_ctor_get(v_toApplicative_8856_, 1);
    leanh::lean_inc_n(v_toPure_8859_, 2);
    leanh::lean_inc_n(v_inst_8849_, 2);
    v_x_8860_ = leanh::lean_alloc_closure(
        l_Lean_Meta_transformWithCache___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v_x_8860_, 0, v_inst_8849_);
    v___x_8861_ = 0;
    v___x_8862_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Core_transform___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Core_transform___redArg___closed__2_once),
        _init_l_Lean_Core_transform___redArg___closed__2,
    );
    v___x_8863_ = l_Lean_Meta_transformWithCache___redArg___lam__1(
        v_inst_8849_,
        leanh::lean_box(0),
        v___x_8862_,
    );
    v___f_8864_ = leanh::lean_alloc_closure(
        l_Lean_Core_transform___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_8864_, 0, v_toPure_8859_);
    v___x_8865_ = leanh::lean_box((v_usedLetOnly_8854_) as usize);
    v___x_8866_ = leanh::lean_box((v_skipConstInApp_8855_) as usize);
    v___x_8867_ = leanh::lean_box((v___x_8861_) as usize);
    v___f_8868_ = leanh::lean_alloc_closure(
        l_Lean_Meta_transform___redArg___lam__5___boxed as *mut core::ffi::c_void,
        14,
        13,
    );
    leanh::lean_closure_set(v___f_8868_, 0, v_toPure_8859_);
    leanh::lean_closure_set(v___f_8868_, 1, v_x_8860_);
    leanh::lean_closure_set(v___f_8868_, 2, v_toBind_8857_);
    leanh::lean_closure_set(v___f_8868_, 3, v_inst_8848_);
    leanh::lean_closure_set(v___f_8868_, 4, v_inst_8849_);
    leanh::lean_closure_set(v___f_8868_, 5, v_inst_8850_);
    leanh::lean_closure_set(v___f_8868_, 6, v_pre_8852_);
    leanh::lean_closure_set(v___f_8868_, 7, v_post_8853_);
    leanh::lean_closure_set(v___f_8868_, 8, v___x_8865_);
    leanh::lean_closure_set(v___f_8868_, 9, v___x_8866_);
    leanh::lean_closure_set(v___f_8868_, 10, v___x_8867_);
    leanh::lean_closure_set(v___f_8868_, 11, v_x_8858_);
    leanh::lean_closure_set(v___f_8868_, 12, v_input_8851_);
    v___x_8869_ = leanh::lean_apply_4(
        v_toBind_8857_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_8863_,
        v___f_8868_,
    );
    v___x_8870_ = leanh::lean_apply_4(
        v_toBind_8857_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_8869_,
        v___f_8864_,
    );
    return v___x_8870_;
}
pub unsafe fn l_Lean_Meta_transform___redArg___boxed(
    mut v_inst_8871_: *mut leanh::LeanObject,
    mut v_inst_8872_: *mut leanh::LeanObject,
    mut v_inst_8873_: *mut leanh::LeanObject,
    mut v_input_8874_: *mut leanh::LeanObject,
    mut v_pre_8875_: *mut leanh::LeanObject,
    mut v_post_8876_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8877_: *mut leanh::LeanObject,
    mut v_skipConstInApp_8878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_8879_: u8 = 0;
    let mut v_skipConstInApp_boxed_8880_: u8 = 0;
    let mut v_res_8881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_8879_ = (leanh::lean_unbox(v_usedLetOnly_8877_) as u8);
    v_skipConstInApp_boxed_8880_ = (leanh::lean_unbox(v_skipConstInApp_8878_) as u8);
    v_res_8881_ = l_Lean_Meta_transform___redArg(
        v_inst_8871_,
        v_inst_8872_,
        v_inst_8873_,
        v_input_8874_,
        v_pre_8875_,
        v_post_8876_,
        v_usedLetOnly_boxed_8879_,
        v_skipConstInApp_boxed_8880_,
    );
    return v_res_8881_;
}
pub unsafe fn l_Lean_Meta_transform(
    mut v_m_8882_: *mut leanh::LeanObject,
    mut v_inst_8883_: *mut leanh::LeanObject,
    mut v_inst_8884_: *mut leanh::LeanObject,
    mut v_inst_8885_: *mut leanh::LeanObject,
    mut v_input_8886_: *mut leanh::LeanObject,
    mut v_pre_8887_: *mut leanh::LeanObject,
    mut v_post_8888_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8889_: u8,
    mut v_skipConstInApp_8890_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_8891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8891_ = l_Lean_Meta_transform___redArg(
        v_inst_8883_,
        v_inst_8884_,
        v_inst_8885_,
        v_input_8886_,
        v_pre_8887_,
        v_post_8888_,
        v_usedLetOnly_8889_,
        v_skipConstInApp_8890_,
    );
    return v___x_8891_;
}
pub unsafe fn l_Lean_Meta_transform___boxed(
    mut v_m_8892_: *mut leanh::LeanObject,
    mut v_inst_8893_: *mut leanh::LeanObject,
    mut v_inst_8894_: *mut leanh::LeanObject,
    mut v_inst_8895_: *mut leanh::LeanObject,
    mut v_input_8896_: *mut leanh::LeanObject,
    mut v_pre_8897_: *mut leanh::LeanObject,
    mut v_post_8898_: *mut leanh::LeanObject,
    mut v_usedLetOnly_8899_: *mut leanh::LeanObject,
    mut v_skipConstInApp_8900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_8901_: u8 = 0;
    let mut v_skipConstInApp_boxed_8902_: u8 = 0;
    let mut v_res_8903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_8901_ = (leanh::lean_unbox(v_usedLetOnly_8899_) as u8);
    v_skipConstInApp_boxed_8902_ = (leanh::lean_unbox(v_skipConstInApp_8900_) as u8);
    v_res_8903_ = l_Lean_Meta_transform(
        v_m_8892_,
        v_inst_8893_,
        v_inst_8894_,
        v_inst_8895_,
        v_input_8896_,
        v_pre_8897_,
        v_post_8898_,
        v_usedLetOnly_boxed_8901_,
        v_skipConstInApp_boxed_8902_,
    );
    return v_res_8903_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(
    mut v_e_8904_: *mut leanh::LeanObject,
    mut v___y_8905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8907_: u8 = 0;
    let mut v___x_8908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_8910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_8912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_8915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_8916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_8917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_8918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8921_: u8 = 0;
    let mut v___x_8923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8927_: u8 = 0;
    let mut v_unused_8928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8907_ = l_Lean_Expr_hasMVar(v_e_8904_);
                if v___x_8907_ == 0 {
                    v___x_8908_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8908_, 0, v_e_8904_);
                    return v___x_8908_;
                } else {
                    v___x_8909_ = lean_st_ref_get(v___y_8905_);
                    v_mctx_8910_ = leanh::lean_ctor_get(v___x_8909_, 0);
                    leanh::lean_inc_ref(v_mctx_8910_);
                    leanh::lean_dec(v___x_8909_);
                    v___x_8911_ = l_Lean_instantiateMVarsCore(v_mctx_8910_, v_e_8904_);
                    v_fst_8912_ = leanh::lean_ctor_get(v___x_8911_, 0);
                    leanh::lean_inc(v_fst_8912_);
                    v_snd_8913_ = leanh::lean_ctor_get(v___x_8911_, 1);
                    leanh::lean_inc(v_snd_8913_);
                    leanh::lean_dec_ref(v___x_8911_);
                    v___x_8914_ = lean_st_ref_take(v___y_8905_);
                    v_cache_8915_ = leanh::lean_ctor_get(v___x_8914_, 1);
                    v_zetaDeltaFVarIds_8916_ = leanh::lean_ctor_get(v___x_8914_, 2);
                    v_postponed_8917_ = leanh::lean_ctor_get(v___x_8914_, 3);
                    v_diag_8918_ = leanh::lean_ctor_get(v___x_8914_, 4);
                    v_isSharedCheck_8927_ = (!leanh::lean_is_exclusive(v___x_8914_)) as u8;
                    if v_isSharedCheck_8927_ == 0 {
                        v_unused_8928_ = leanh::lean_ctor_get(v___x_8914_, 0);
                        leanh::lean_dec(v_unused_8928_);
                        v___x_8920_ = v___x_8914_;
                        v_isShared_8921_ = v_isSharedCheck_8927_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_8918_);
                        leanh::lean_inc(v_postponed_8917_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_8916_);
                        leanh::lean_inc(v_cache_8915_);
                        leanh::lean_dec(v___x_8914_);
                        v___x_8920_ = leanh::lean_box(0);
                        v_isShared_8921_ = v_isSharedCheck_8927_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8921_ == 0 {
                    leanh::lean_ctor_set(v___x_8920_, 0, v_snd_8913_);
                    v___x_8923_ = v___x_8920_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8926_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8926_, 0, v_snd_8913_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8926_, 1, v_cache_8915_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_8926_,
                        2,
                        v_zetaDeltaFVarIds_8916_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_8926_, 3, v_postponed_8917_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8926_, 4, v_diag_8918_);
                    v___x_8923_ = v_reuseFailAlloc_8926_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8924_ = lean_st_ref_set(v___y_8905_, v___x_8923_);
                v___x_8925_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_8925_, 0, v_fst_8912_);
                return v___x_8925_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg___boxed(
    mut v_e_8929_: *mut leanh::LeanObject,
    mut v___y_8930_: *mut leanh::LeanObject,
    mut v___y_8931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8932_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(
        v_e_8929_,
        v___y_8930_,
    );
    leanh::lean_dec(v___y_8930_);
    return v_res_8932_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(
    mut v_e_8933_: *mut leanh::LeanObject,
    mut v___y_8934_: *mut leanh::LeanObject,
    mut v___y_8935_: *mut leanh::LeanObject,
    mut v___y_8936_: *mut leanh::LeanObject,
    mut v___y_8937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8939_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(
        v_e_8933_,
        v___y_8935_,
    );
    return v___x_8939_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___boxed(
    mut v_e_8940_: *mut leanh::LeanObject,
    mut v___y_8941_: *mut leanh::LeanObject,
    mut v___y_8942_: *mut leanh::LeanObject,
    mut v___y_8943_: *mut leanh::LeanObject,
    mut v___y_8944_: *mut leanh::LeanObject,
    mut v___y_8945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8946_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(
        v_e_8940_,
        v___y_8941_,
        v___y_8942_,
        v___y_8943_,
        v___y_8944_,
    );
    leanh::lean_dec(v___y_8944_);
    leanh::lean_dec_ref(v___y_8943_);
    leanh::lean_dec(v___y_8942_);
    leanh::lean_dec_ref(v___y_8941_);
    return v_res_8946_;
}
pub unsafe fn l_Lean_Meta_zetaReduce___lam__0(
    mut v_zetaHave_8947_: u8,
    mut v___x_8948_: *mut leanh::LeanObject,
    mut v_zetaDelta_8949_: u8,
    mut v_fvarId_8950_: *mut leanh::LeanObject,
    mut v___y_8951_: *mut leanh::LeanObject,
    mut v___y_8952_: *mut leanh::LeanObject,
    mut v___y_8953_: *mut leanh::LeanObject,
    mut v___y_8954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8960_: u8 = 0;
    let mut v_val_8961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8964_: u8 = 0;
    let mut v___y_8966_: u8 = 0;
    let mut v___x_8967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8973_: u8 = 0;
    let mut v___x_8974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8975_: u8 = 0;
    let mut v___x_8976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8980_: u8 = 0;
    let mut v___x_8981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8985_: u8 = 0;
    let mut v_a_8986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8989_: u8 = 0;
    let mut v___x_8991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8993_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8956_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_8950_, v___y_8951_);
                if leanh::lean_obj_tag(v___x_8956_) == 0 {
                    v_a_8957_ = leanh::lean_ctor_get(v___x_8956_, 0);
                    v_isSharedCheck_8985_ = (!leanh::lean_is_exclusive(v___x_8956_)) as u8;
                    if v_isSharedCheck_8985_ == 0 {
                        v___x_8959_ = v___x_8956_;
                        v_isShared_8960_ = v_isSharedCheck_8985_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8957_);
                        leanh::lean_dec(v___x_8956_);
                        v___x_8959_ = leanh::lean_box(0);
                        v_isShared_8960_ = v_isSharedCheck_8985_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8986_ = leanh::lean_ctor_get(v___x_8956_, 0);
                    v_isSharedCheck_8993_ = (!leanh::lean_is_exclusive(v___x_8956_)) as u8;
                    if v_isSharedCheck_8993_ == 0 {
                        v___x_8988_ = v___x_8956_;
                        v_isShared_8989_ = v_isSharedCheck_8993_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8986_);
                        leanh::lean_dec(v___x_8956_);
                        v___x_8988_ = leanh::lean_box(0);
                        v_isShared_8989_ = v_isSharedCheck_8993_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_8957_) == 1 {
                    v_val_8961_ = leanh::lean_ctor_get(v_a_8957_, 0);
                    v_isSharedCheck_8980_ = (!leanh::lean_is_exclusive(v_a_8957_)) as u8;
                    if v_isSharedCheck_8980_ == 0 {
                        v___x_8963_ = v_a_8957_;
                        v_isShared_8964_ = v_isSharedCheck_8980_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_8961_);
                        leanh::lean_dec(v_a_8957_);
                        v___x_8963_ = leanh::lean_box(0);
                        v_isShared_8964_ = v_isSharedCheck_8980_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_8957_);
                    v___x_8981_ = leanh::lean_box(0);
                    if v_isShared_8960_ == 0 {
                        leanh::lean_ctor_set(v___x_8959_, 0, v___x_8981_);
                        v___x_8983_ = v___x_8959_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_8984_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8984_, 0, v___x_8981_);
                        v___x_8983_ = v_reuseFailAlloc_8984_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if v_zetaDelta_8949_ == 0 {
                    v___x_8974_ = l_Lean_LocalDecl_index(v_val_8961_);
                    v___x_8975_ = lean_nat_dec_lt(v___x_8974_, v___x_8948_);
                    leanh::lean_dec(v___x_8974_);
                    if v___x_8975_ == 0 {
                        leanh::lean_del_object(v___x_8963_);
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v_val_8961_);
                        leanh::lean_del_object(v___x_8959_);
                        v___x_8976_ = leanh::lean_box(0);
                        if v_isShared_8964_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_8963_, 0);
                            leanh::lean_ctor_set(v___x_8963_, 0, v___x_8976_);
                            v___x_8978_ = v___x_8963_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_8979_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_8979_, 0, v___x_8976_);
                            v___x_8978_ = v_reuseFailAlloc_8979_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_8963_);
                    state = 5;
                    continue;
                }
            }
            3 => {
                v___x_8967_ = l_Lean_LocalDecl_value_x3f(v_val_8961_, v___y_8966_);
                leanh::lean_dec(v_val_8961_);
                if v_isShared_8960_ == 0 {
                    leanh::lean_ctor_set(v___x_8959_, 0, v___x_8967_);
                    v___x_8969_ = v___x_8959_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8970_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8970_, 0, v___x_8967_);
                    v___x_8969_ = v_reuseFailAlloc_8970_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8969_;
            }
            5 => {
                if v_zetaHave_8947_ == 0 {
                    v___y_8966_ = v_zetaHave_8947_;
                    state = 3;
                    continue;
                } else {
                    v___x_8972_ = l_Lean_LocalDecl_index(v_val_8961_);
                    v___x_8973_ = lean_nat_dec_le(v___x_8948_, v___x_8972_);
                    leanh::lean_dec(v___x_8972_);
                    v___y_8966_ = v___x_8973_;
                    state = 3;
                    continue;
                }
            }
            6 => {
                return v___x_8978_;
            }
            7 => {
                return v___x_8983_;
            }
            8 => {
                if v_isShared_8989_ == 0 {
                    v___x_8991_ = v___x_8988_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8992_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8992_, 0, v_a_8986_);
                    v___x_8991_ = v_reuseFailAlloc_8992_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_8991_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_zetaReduce___lam__0___boxed(
    mut v_zetaHave_8994_: *mut leanh::LeanObject,
    mut v___x_8995_: *mut leanh::LeanObject,
    mut v_zetaDelta_8996_: *mut leanh::LeanObject,
    mut v_fvarId_8997_: *mut leanh::LeanObject,
    mut v___y_8998_: *mut leanh::LeanObject,
    mut v___y_8999_: *mut leanh::LeanObject,
    mut v___y_9000_: *mut leanh::LeanObject,
    mut v___y_9001_: *mut leanh::LeanObject,
    mut v___y_9002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zetaHave_boxed_9003_: u8 = 0;
    let mut v_zetaDelta_boxed_9004_: u8 = 0;
    let mut v_res_9005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_zetaHave_boxed_9003_ = (leanh::lean_unbox(v_zetaHave_8994_) as u8);
    v_zetaDelta_boxed_9004_ = (leanh::lean_unbox(v_zetaDelta_8996_) as u8);
    v_res_9005_ = l_Lean_Meta_zetaReduce___lam__0(
        v_zetaHave_boxed_9003_,
        v___x_8995_,
        v_zetaDelta_boxed_9004_,
        v_fvarId_8997_,
        v___y_8998_,
        v___y_8999_,
        v___y_9000_,
        v___y_9001_,
    );
    leanh::lean_dec(v___y_9001_);
    leanh::lean_dec_ref(v___y_9000_);
    leanh::lean_dec(v___y_8999_);
    leanh::lean_dec_ref(v___y_8998_);
    leanh::lean_dec(v___x_8995_);
    return v_res_9005_;
}
pub unsafe fn l_Lean_Meta_zetaReduce___lam__1(
    mut v_e_9006_: *mut leanh::LeanObject,
    mut v___y_9007_: *mut leanh::LeanObject,
    mut v___y_9008_: *mut leanh::LeanObject,
    mut v___y_9009_: *mut leanh::LeanObject,
    mut v___y_9010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9012_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_9012_, 0, v_e_9006_);
    v___x_9013_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_9013_, 0, v___x_9012_);
    return v___x_9013_;
}
pub unsafe fn l_Lean_Meta_zetaReduce___lam__1___boxed(
    mut v_e_9014_: *mut leanh::LeanObject,
    mut v___y_9015_: *mut leanh::LeanObject,
    mut v___y_9016_: *mut leanh::LeanObject,
    mut v___y_9017_: *mut leanh::LeanObject,
    mut v___y_9018_: *mut leanh::LeanObject,
    mut v___y_9019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9020_ = l_Lean_Meta_zetaReduce___lam__1(
        v_e_9014_,
        v___y_9015_,
        v___y_9016_,
        v___y_9017_,
        v___y_9018_,
    );
    leanh::lean_dec(v___y_9018_);
    leanh::lean_dec_ref(v___y_9017_);
    leanh::lean_dec(v___y_9016_);
    leanh::lean_dec_ref(v___y_9015_);
    return v_res_9020_;
}
pub unsafe fn l_Lean_Meta_zetaReduce___lam__2(
    mut v___f_9021_: *mut leanh::LeanObject,
    mut v_e_9022_: *mut leanh::LeanObject,
    mut v___y_9023_: *mut leanh::LeanObject,
    mut v___y_9024_: *mut leanh::LeanObject,
    mut v___y_9025_: *mut leanh::LeanObject,
    mut v___y_9026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fvarId_9028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9033_: u8 = 0;
    let mut v_val_9034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9037_: u8 = 0;
    let mut v___x_9038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9042_: u8 = 0;
    let mut v___x_9044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9049_: u8 = 0;
    let mut v_isSharedCheck_9050_: u8 = 0;
    let mut v___x_9051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9055_: u8 = 0;
    let mut v_a_9056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9059_: u8 = 0;
    let mut v___x_9061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9063_: u8 = 0;
    let mut v___x_9064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_e_9022_) == 1 {
                    v_fvarId_9028_ = leanh::lean_ctor_get(v_e_9022_, 0);
                    leanh::lean_inc(v___y_9026_);
                    leanh::lean_inc_ref(v___y_9025_);
                    leanh::lean_inc(v___y_9024_);
                    leanh::lean_inc_ref(v___y_9023_);
                    leanh::lean_inc(v_fvarId_9028_);
                    v___x_9029_ = leanh::lean_apply_6(
                        v___f_9021_,
                        v_fvarId_9028_,
                        v___y_9023_,
                        v___y_9024_,
                        v___y_9025_,
                        v___y_9026_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_9029_) == 0 {
                        v_a_9030_ = leanh::lean_ctor_get(v___x_9029_, 0);
                        v_isSharedCheck_9055_ =
                            (!leanh::lean_is_exclusive(v___x_9029_)) as u8;
                        if v_isSharedCheck_9055_ == 0 {
                            v___x_9032_ = v___x_9029_;
                            v_isShared_9033_ = v_isSharedCheck_9055_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_9030_);
                            leanh::lean_dec(v___x_9029_);
                            v___x_9032_ = leanh::lean_box(0);
                            v_isShared_9033_ = v_isSharedCheck_9055_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_e_9022_, 1);
                        v_a_9056_ = leanh::lean_ctor_get(v___x_9029_, 0);
                        v_isSharedCheck_9063_ =
                            (!leanh::lean_is_exclusive(v___x_9029_)) as u8;
                        if v_isSharedCheck_9063_ == 0 {
                            v___x_9058_ = v___x_9029_;
                            v_isShared_9059_ = v_isSharedCheck_9063_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_9056_);
                            leanh::lean_dec(v___x_9029_);
                            v___x_9058_ = leanh::lean_box(0);
                            v_isShared_9059_ = v_isSharedCheck_9063_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_9022_);
                    leanh::lean_dec_ref(v___f_9021_);
                    v___x_9064_ = l_Lean_Core_betaReduce___lam__0___closed__0;
                    v___x_9065_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_9065_, 0, v___x_9064_);
                    return v___x_9065_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_9030_) == 1 {
                    leanh::lean_del_object(v___x_9032_);
                    leanh::lean_dec_ref_known(v_e_9022_, 1);
                    v_val_9034_ = leanh::lean_ctor_get(v_a_9030_, 0);
                    v_isSharedCheck_9050_ = (!leanh::lean_is_exclusive(v_a_9030_)) as u8;
                    if v_isSharedCheck_9050_ == 0 {
                        v___x_9036_ = v_a_9030_;
                        v_isShared_9037_ = v_isSharedCheck_9050_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_9034_);
                        leanh::lean_dec(v_a_9030_);
                        v___x_9036_ = leanh::lean_box(0);
                        v_isShared_9037_ = v_isSharedCheck_9050_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_9030_);
                    v___x_9051_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_9051_, 0, v_e_9022_);
                    if v_isShared_9033_ == 0 {
                        leanh::lean_ctor_set(v___x_9032_, 0, v___x_9051_);
                        v___x_9053_ = v___x_9032_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_9054_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_9054_, 0, v___x_9051_);
                        v___x_9053_ = v_reuseFailAlloc_9054_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_9038_ =
                    l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(
                        v_val_9034_,
                        v___y_9024_,
                    );
                v_a_9039_ = leanh::lean_ctor_get(v___x_9038_, 0);
                v_isSharedCheck_9049_ = (!leanh::lean_is_exclusive(v___x_9038_)) as u8;
                if v_isSharedCheck_9049_ == 0 {
                    v___x_9041_ = v___x_9038_;
                    v_isShared_9042_ = v_isSharedCheck_9049_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_a_9039_);
                    leanh::lean_dec(v___x_9038_);
                    v___x_9041_ = leanh::lean_box(0);
                    v_isShared_9042_ = v_isSharedCheck_9049_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_9037_ == 0 {
                    leanh::lean_ctor_set(v___x_9036_, 0, v_a_9039_);
                    v___x_9044_ = v___x_9036_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9048_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9048_, 0, v_a_9039_);
                    v___x_9044_ = v_reuseFailAlloc_9048_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_9042_ == 0 {
                    leanh::lean_ctor_set(v___x_9041_, 0, v___x_9044_);
                    v___x_9046_ = v___x_9041_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_9047_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9047_, 0, v___x_9044_);
                    v___x_9046_ = v_reuseFailAlloc_9047_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_9046_;
            }
            6 => {
                return v___x_9053_;
            }
            7 => {
                if v_isShared_9059_ == 0 {
                    v___x_9061_ = v___x_9058_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_9062_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9062_, 0, v_a_9056_);
                    v___x_9061_ = v_reuseFailAlloc_9062_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_9061_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_zetaReduce___lam__2___boxed(
    mut v___f_9066_: *mut leanh::LeanObject,
    mut v_e_9067_: *mut leanh::LeanObject,
    mut v___y_9068_: *mut leanh::LeanObject,
    mut v___y_9069_: *mut leanh::LeanObject,
    mut v___y_9070_: *mut leanh::LeanObject,
    mut v___y_9071_: *mut leanh::LeanObject,
    mut v___y_9072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9073_ = l_Lean_Meta_zetaReduce___lam__2(
        v___f_9066_,
        v_e_9067_,
        v___y_9068_,
        v___y_9069_,
        v___y_9070_,
        v___y_9071_,
    );
    leanh::lean_dec(v___y_9071_);
    leanh::lean_dec_ref(v___y_9070_);
    leanh::lean_dec(v___y_9069_);
    leanh::lean_dec_ref(v___y_9068_);
    return v_res_9073_;
}
pub unsafe fn l_Lean_Meta_zetaReduce___lam__4(
    mut v___f_9074_: *mut leanh::LeanObject,
    mut v_e_9075_: *mut leanh::LeanObject,
    mut v___y_9076_: *mut leanh::LeanObject,
    mut v___y_9077_: *mut leanh::LeanObject,
    mut v___y_9078_: *mut leanh::LeanObject,
    mut v___y_9079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_9082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9087_: u8 = 0;
    let mut v_val_9088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9091_: u8 = 0;
    let mut v___x_9092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9096_: u8 = 0;
    let mut v_dummy_9097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_9098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9110_: u8 = 0;
    let mut v_isSharedCheck_9111_: u8 = 0;
    let mut v___x_9112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9116_: u8 = 0;
    let mut v_a_9117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9120_: u8 = 0;
    let mut v___x_9122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9124_: u8 = 0;
    let mut v___x_9125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9081_ = l_Lean_Expr_getAppFn(v_e_9075_);
                if leanh::lean_obj_tag(v___x_9081_) == 1 {
                    v_fvarId_9082_ = leanh::lean_ctor_get(v___x_9081_, 0);
                    leanh::lean_inc(v_fvarId_9082_);
                    leanh::lean_dec_ref_known(v___x_9081_, 1);
                    leanh::lean_inc(v___y_9079_);
                    leanh::lean_inc_ref(v___y_9078_);
                    leanh::lean_inc(v___y_9077_);
                    leanh::lean_inc_ref(v___y_9076_);
                    v___x_9083_ = leanh::lean_apply_6(
                        v___f_9074_,
                        v_fvarId_9082_,
                        v___y_9076_,
                        v___y_9077_,
                        v___y_9078_,
                        v___y_9079_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_9083_) == 0 {
                        v_a_9084_ = leanh::lean_ctor_get(v___x_9083_, 0);
                        v_isSharedCheck_9116_ =
                            (!leanh::lean_is_exclusive(v___x_9083_)) as u8;
                        if v_isSharedCheck_9116_ == 0 {
                            v___x_9086_ = v___x_9083_;
                            v_isShared_9087_ = v_isSharedCheck_9116_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_9084_);
                            leanh::lean_dec(v___x_9083_);
                            v___x_9086_ = leanh::lean_box(0);
                            v_isShared_9087_ = v_isSharedCheck_9116_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_9075_);
                        v_a_9117_ = leanh::lean_ctor_get(v___x_9083_, 0);
                        v_isSharedCheck_9124_ =
                            (!leanh::lean_is_exclusive(v___x_9083_)) as u8;
                        if v_isSharedCheck_9124_ == 0 {
                            v___x_9119_ = v___x_9083_;
                            v_isShared_9120_ = v_isSharedCheck_9124_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_9117_);
                            leanh::lean_dec(v___x_9083_);
                            v___x_9119_ = leanh::lean_box(0);
                            v_isShared_9120_ = v_isSharedCheck_9124_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_9081_);
                    leanh::lean_dec_ref(v_e_9075_);
                    leanh::lean_dec_ref(v___f_9074_);
                    v___x_9125_ = l_Lean_Core_betaReduce___lam__0___closed__0;
                    v___x_9126_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_9126_, 0, v___x_9125_);
                    return v___x_9126_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_9084_) == 1 {
                    leanh::lean_del_object(v___x_9086_);
                    v_val_9088_ = leanh::lean_ctor_get(v_a_9084_, 0);
                    v_isSharedCheck_9111_ = (!leanh::lean_is_exclusive(v_a_9084_)) as u8;
                    if v_isSharedCheck_9111_ == 0 {
                        v___x_9090_ = v_a_9084_;
                        v_isShared_9091_ = v_isSharedCheck_9111_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_9088_);
                        leanh::lean_dec(v_a_9084_);
                        v___x_9090_ = leanh::lean_box(0);
                        v_isShared_9091_ = v_isSharedCheck_9111_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_9084_);
                    leanh::lean_dec_ref(v_e_9075_);
                    v___x_9112_ = l_Lean_Core_betaReduce___lam__0___closed__0;
                    if v_isShared_9087_ == 0 {
                        leanh::lean_ctor_set(v___x_9086_, 0, v___x_9112_);
                        v___x_9114_ = v___x_9086_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_9115_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_9115_, 0, v___x_9112_);
                        v___x_9114_ = v_reuseFailAlloc_9115_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_9092_ =
                    l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(
                        v_val_9088_,
                        v___y_9077_,
                    );
                v_a_9093_ = leanh::lean_ctor_get(v___x_9092_, 0);
                v_isSharedCheck_9110_ = (!leanh::lean_is_exclusive(v___x_9092_)) as u8;
                if v_isSharedCheck_9110_ == 0 {
                    v___x_9095_ = v___x_9092_;
                    v_isShared_9096_ = v_isSharedCheck_9110_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_a_9093_);
                    leanh::lean_dec(v___x_9092_);
                    v___x_9095_ = leanh::lean_box(0);
                    v_isShared_9096_ = v_isSharedCheck_9110_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_dummy_9097_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once), _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
                v_nargs_9098_ = l_Lean_Expr_getAppNumArgs(v_e_9075_);
                leanh::lean_inc(v_nargs_9098_);
                v___x_9099_ = lean_mk_array(v_nargs_9098_, v_dummy_9097_);
                v___x_9100_ = leanh::lean_unsigned_to_nat(1);
                v___x_9101_ = lean_nat_sub(v_nargs_9098_, v___x_9100_);
                leanh::lean_dec(v_nargs_9098_);
                v___x_9102_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_e_9075_,
                    v___x_9099_,
                    v___x_9101_,
                );
                v___x_9103_ = l_Lean_Expr_beta(v_a_9093_, v___x_9102_);
                if v_isShared_9091_ == 0 {
                    leanh::lean_ctor_set(v___x_9090_, 0, v___x_9103_);
                    v___x_9105_ = v___x_9090_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9109_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9109_, 0, v___x_9103_);
                    v___x_9105_ = v_reuseFailAlloc_9109_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_9096_ == 0 {
                    leanh::lean_ctor_set(v___x_9095_, 0, v___x_9105_);
                    v___x_9107_ = v___x_9095_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_9108_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9108_, 0, v___x_9105_);
                    v___x_9107_ = v_reuseFailAlloc_9108_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_9107_;
            }
            6 => {
                return v___x_9114_;
            }
            7 => {
                if v_isShared_9120_ == 0 {
                    v___x_9122_ = v___x_9119_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_9123_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9123_, 0, v_a_9117_);
                    v___x_9122_ = v_reuseFailAlloc_9123_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_9122_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_zetaReduce___lam__4___boxed(
    mut v___f_9127_: *mut leanh::LeanObject,
    mut v_e_9128_: *mut leanh::LeanObject,
    mut v___y_9129_: *mut leanh::LeanObject,
    mut v___y_9130_: *mut leanh::LeanObject,
    mut v___y_9131_: *mut leanh::LeanObject,
    mut v___y_9132_: *mut leanh::LeanObject,
    mut v___y_9133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9134_ = l_Lean_Meta_zetaReduce___lam__4(
        v___f_9127_,
        v_e_9128_,
        v___y_9129_,
        v___y_9130_,
        v___y_9131_,
        v___y_9132_,
    );
    leanh::lean_dec(v___y_9132_);
    leanh::lean_dec_ref(v___y_9131_);
    leanh::lean_dec(v___y_9130_);
    leanh::lean_dec_ref(v___y_9129_);
    return v_res_9134_;
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(
    mut v_00_u03b1_9135_: *mut leanh::LeanObject,
    mut v_x_9136_: *mut leanh::LeanObject,
    mut v___y_9137_: *mut leanh::LeanObject,
    mut v___y_9138_: *mut leanh::LeanObject,
    mut v___y_9139_: *mut leanh::LeanObject,
    mut v___y_9140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9142_ = leanh::lean_apply_1(v_x_9136_, leanh::lean_box(0));
    v___x_9143_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_9143_, 0, v___x_9142_);
    return v___x_9143_;
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0___boxed(
    mut v_00_u03b1_9144_: *mut leanh::LeanObject,
    mut v_x_9145_: *mut leanh::LeanObject,
    mut v___y_9146_: *mut leanh::LeanObject,
    mut v___y_9147_: *mut leanh::LeanObject,
    mut v___y_9148_: *mut leanh::LeanObject,
    mut v___y_9149_: *mut leanh::LeanObject,
    mut v___y_9150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9151_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(
        v_00_u03b1_9144_,
        v_x_9145_,
        v___y_9146_,
        v___y_9147_,
        v___y_9148_,
        v___y_9149_,
    );
    leanh::lean_dec(v___y_9149_);
    leanh::lean_dec_ref(v___y_9148_);
    leanh::lean_dec(v___y_9147_);
    leanh::lean_dec_ref(v___y_9146_);
    return v_res_9151_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(
    mut v___x_9152_: *mut leanh::LeanObject,
    mut v___y_9153_: *mut leanh::LeanObject,
    mut v___y_9154_: *mut leanh::LeanObject,
    mut v___y_9155_: *mut leanh::LeanObject,
    mut v___y_9156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9158_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_9158_, 0, v___x_9152_);
    return v___x_9158_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(
    mut v___x_9159_: *mut leanh::LeanObject,
    mut v___y_9160_: *mut leanh::LeanObject,
    mut v___y_9161_: *mut leanh::LeanObject,
    mut v___y_9162_: *mut leanh::LeanObject,
    mut v___y_9163_: *mut leanh::LeanObject,
    mut v___y_9164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9165_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_9159_, v___y_9160_, v___y_9161_, v___y_9162_, v___y_9163_);
    leanh::lean_dec(v___y_9163_);
    leanh::lean_dec_ref(v___y_9162_);
    leanh::lean_dec(v___y_9161_);
    leanh::lean_dec_ref(v___y_9160_);
    return v_res_9165_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(
    mut v_k_9166_: *mut leanh::LeanObject,
    mut v___y_9167_: *mut leanh::LeanObject,
    mut v_b_9168_: *mut leanh::LeanObject,
    mut v___y_9169_: *mut leanh::LeanObject,
    mut v___y_9170_: *mut leanh::LeanObject,
    mut v___y_9171_: *mut leanh::LeanObject,
    mut v___y_9172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9174_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_9172_);
    leanh::lean_inc_ref(v___y_9171_);
    leanh::lean_inc(v___y_9170_);
    leanh::lean_inc_ref(v___y_9169_);
    leanh::lean_inc(v___y_9167_);
    v___x_9174_ = leanh::lean_apply_7(
        v_k_9166_,
        v_b_9168_,
        v___y_9167_,
        v___y_9169_,
        v___y_9170_,
        v___y_9171_,
        v___y_9172_,
        leanh::lean_box(0),
    );
    return v___x_9174_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed(
    mut v_k_9175_: *mut leanh::LeanObject,
    mut v___y_9176_: *mut leanh::LeanObject,
    mut v_b_9177_: *mut leanh::LeanObject,
    mut v___y_9178_: *mut leanh::LeanObject,
    mut v___y_9179_: *mut leanh::LeanObject,
    mut v___y_9180_: *mut leanh::LeanObject,
    mut v___y_9181_: *mut leanh::LeanObject,
    mut v___y_9182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9183_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(v_k_9175_, v___y_9176_, v_b_9177_, v___y_9178_, v___y_9179_, v___y_9180_, v___y_9181_);
    leanh::lean_dec(v___y_9181_);
    leanh::lean_dec_ref(v___y_9180_);
    leanh::lean_dec(v___y_9179_);
    leanh::lean_dec_ref(v___y_9178_);
    leanh::lean_dec(v___y_9176_);
    return v_res_9183_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(
    mut v_name_9184_: *mut leanh::LeanObject,
    mut v_bi_9185_: u8,
    mut v_type_9186_: *mut leanh::LeanObject,
    mut v_k_9187_: *mut leanh::LeanObject,
    mut v_kind_9188_: u8,
    mut v___y_9189_: *mut leanh::LeanObject,
    mut v___y_9190_: *mut leanh::LeanObject,
    mut v___y_9191_: *mut leanh::LeanObject,
    mut v___y_9192_: *mut leanh::LeanObject,
    mut v___y_9193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_9195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9200_: u8 = 0;
    let mut v___x_9202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9204_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_9189_);
                v___f_9195_ = leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
                leanh::lean_closure_set(v___f_9195_, 0, v_k_9187_);
                leanh::lean_closure_set(v___f_9195_, 1, v___y_9189_);
                v___x_9196_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    leanh::lean_box(0),
                    v_name_9184_,
                    v_bi_9185_,
                    v_type_9186_,
                    v___f_9195_,
                    v_kind_9188_,
                    v___y_9190_,
                    v___y_9191_,
                    v___y_9192_,
                    v___y_9193_,
                );
                if leanh::lean_obj_tag(v___x_9196_) == 0 {
                    return v___x_9196_;
                } else {
                    v_a_9197_ = leanh::lean_ctor_get(v___x_9196_, 0);
                    v_isSharedCheck_9204_ = (!leanh::lean_is_exclusive(v___x_9196_)) as u8;
                    if v_isSharedCheck_9204_ == 0 {
                        v___x_9199_ = v___x_9196_;
                        v_isShared_9200_ = v_isSharedCheck_9204_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9197_);
                        leanh::lean_dec(v___x_9196_);
                        v___x_9199_ = leanh::lean_box(0);
                        v_isShared_9200_ = v_isSharedCheck_9204_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_9200_ == 0 {
                    v___x_9202_ = v___x_9199_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9203_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9203_, 0, v_a_9197_);
                    v___x_9202_ = v_reuseFailAlloc_9203_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9202_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(
    mut v_name_9205_: *mut leanh::LeanObject,
    mut v_bi_9206_: *mut leanh::LeanObject,
    mut v_type_9207_: *mut leanh::LeanObject,
    mut v_k_9208_: *mut leanh::LeanObject,
    mut v_kind_9209_: *mut leanh::LeanObject,
    mut v___y_9210_: *mut leanh::LeanObject,
    mut v___y_9211_: *mut leanh::LeanObject,
    mut v___y_9212_: *mut leanh::LeanObject,
    mut v___y_9213_: *mut leanh::LeanObject,
    mut v___y_9214_: *mut leanh::LeanObject,
    mut v___y_9215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_9216_: u8 = 0;
    let mut v_kind_boxed_9217_: u8 = 0;
    let mut v_res_9218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_9216_ = (leanh::lean_unbox(v_bi_9206_) as u8);
    v_kind_boxed_9217_ = (leanh::lean_unbox(v_kind_9209_) as u8);
    v_res_9218_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_9205_, v_bi_boxed_9216_, v_type_9207_, v_k_9208_, v_kind_boxed_9217_, v___y_9210_, v___y_9211_, v___y_9212_, v___y_9213_, v___y_9214_);
    leanh::lean_dec(v___y_9214_);
    leanh::lean_dec_ref(v___y_9213_);
    leanh::lean_dec(v___y_9212_);
    leanh::lean_dec_ref(v___y_9211_);
    leanh::lean_dec(v___y_9210_);
    return v_res_9218_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(
    mut v_name_9219_: *mut leanh::LeanObject,
    mut v_type_9220_: *mut leanh::LeanObject,
    mut v_val_9221_: *mut leanh::LeanObject,
    mut v_k_9222_: *mut leanh::LeanObject,
    mut v_nondep_9223_: u8,
    mut v_kind_9224_: u8,
    mut v___y_9225_: *mut leanh::LeanObject,
    mut v___y_9226_: *mut leanh::LeanObject,
    mut v___y_9227_: *mut leanh::LeanObject,
    mut v___y_9228_: *mut leanh::LeanObject,
    mut v___y_9229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_9231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9236_: u8 = 0;
    let mut v___x_9238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9240_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_9225_);
                v___f_9231_ = leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
                leanh::lean_closure_set(v___f_9231_, 0, v_k_9222_);
                leanh::lean_closure_set(v___f_9231_, 1, v___y_9225_);
                v___x_9232_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(
                    leanh::lean_box(0),
                    v_name_9219_,
                    v_type_9220_,
                    v_val_9221_,
                    v___f_9231_,
                    v_nondep_9223_,
                    v_kind_9224_,
                    v___y_9226_,
                    v___y_9227_,
                    v___y_9228_,
                    v___y_9229_,
                );
                if leanh::lean_obj_tag(v___x_9232_) == 0 {
                    return v___x_9232_;
                } else {
                    v_a_9233_ = leanh::lean_ctor_get(v___x_9232_, 0);
                    v_isSharedCheck_9240_ = (!leanh::lean_is_exclusive(v___x_9232_)) as u8;
                    if v_isSharedCheck_9240_ == 0 {
                        v___x_9235_ = v___x_9232_;
                        v_isShared_9236_ = v_isSharedCheck_9240_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9233_);
                        leanh::lean_dec(v___x_9232_);
                        v___x_9235_ = leanh::lean_box(0);
                        v_isShared_9236_ = v_isSharedCheck_9240_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_9236_ == 0 {
                    v___x_9238_ = v___x_9235_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9239_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9239_, 0, v_a_9233_);
                    v___x_9238_ = v_reuseFailAlloc_9239_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9238_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg___boxed(
    mut v_name_9241_: *mut leanh::LeanObject,
    mut v_type_9242_: *mut leanh::LeanObject,
    mut v_val_9243_: *mut leanh::LeanObject,
    mut v_k_9244_: *mut leanh::LeanObject,
    mut v_nondep_9245_: *mut leanh::LeanObject,
    mut v_kind_9246_: *mut leanh::LeanObject,
    mut v___y_9247_: *mut leanh::LeanObject,
    mut v___y_9248_: *mut leanh::LeanObject,
    mut v___y_9249_: *mut leanh::LeanObject,
    mut v___y_9250_: *mut leanh::LeanObject,
    mut v___y_9251_: *mut leanh::LeanObject,
    mut v___y_9252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_nondep_boxed_9253_: u8 = 0;
    let mut v_kind_boxed_9254_: u8 = 0;
    let mut v_res_9255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_9253_ = (leanh::lean_unbox(v_nondep_9245_) as u8);
    v_kind_boxed_9254_ = (leanh::lean_unbox(v_kind_9246_) as u8);
    v_res_9255_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_9241_, v_type_9242_, v_val_9243_, v_k_9244_, v_nondep_boxed_9253_, v_kind_boxed_9254_, v___y_9247_, v___y_9248_, v___y_9249_, v___y_9250_, v___y_9251_);
    leanh::lean_dec(v___y_9251_);
    leanh::lean_dec_ref(v___y_9250_);
    leanh::lean_dec(v___y_9249_);
    leanh::lean_dec_ref(v___y_9248_);
    leanh::lean_dec(v___y_9247_);
    return v_res_9255_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(
    mut v_00_u03b1_9256_: *mut leanh::LeanObject,
    mut v_x_9257_: *mut leanh::LeanObject,
    mut v___y_9258_: *mut leanh::LeanObject,
    mut v___y_9259_: *mut leanh::LeanObject,
    mut v___y_9260_: *mut leanh::LeanObject,
    mut v___y_9261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9263_ = leanh::lean_apply_1(v_x_9257_, leanh::lean_box(0));
    v___x_9264_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_9264_, 0, v___x_9263_);
    return v___x_9264_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0___boxed(
    mut v_00_u03b1_9265_: *mut leanh::LeanObject,
    mut v_x_9266_: *mut leanh::LeanObject,
    mut v___y_9267_: *mut leanh::LeanObject,
    mut v___y_9268_: *mut leanh::LeanObject,
    mut v___y_9269_: *mut leanh::LeanObject,
    mut v___y_9270_: *mut leanh::LeanObject,
    mut v___y_9271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9272_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(v_00_u03b1_9265_, v_x_9266_, v___y_9267_, v___y_9268_, v___y_9269_, v___y_9270_);
    leanh::lean_dec(v___y_9270_);
    leanh::lean_dec_ref(v___y_9269_);
    leanh::lean_dec(v___y_9268_);
    leanh::lean_dec_ref(v___y_9267_);
    return v_res_9272_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(
    mut v_ref_9273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9275_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
    v___x_9276_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_9276_, 0, v_ref_9273_);
    leanh::lean_ctor_set(v___x_9276_, 1, v___x_9275_);
    v___x_9277_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_9277_, 0, v___x_9276_);
    return v___x_9277_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg___boxed(
    mut v_ref_9278_: *mut leanh::LeanObject,
    mut v___y_9279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9280_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_9278_);
    return v_res_9280_;
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(
    mut v_x_9281_: *mut leanh::LeanObject,
    mut v___y_9282_: *mut leanh::LeanObject,
    mut v___y_9283_: *mut leanh::LeanObject,
    mut v___y_9284_: *mut leanh::LeanObject,
    mut v___y_9285_: *mut leanh::LeanObject,
    mut v___y_9286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_9289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9293_: u8 = 0;
    let mut v___x_9295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9297_: u8 = 0;
    let mut v_fileName_9298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_9299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_9300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_9301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_9302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_9303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_9304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_9305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_9306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_9307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_9308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_9309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_9310_: u8 = 0;
    let mut v_cancelTk_x3f_9311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_9312_: u8 = 0;
    let mut v_inheritedTraceOptions_9313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9320_: u8 = 0;
    let mut v___x_9321_: u8 = 0;
    let mut v___x_9322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_9298_ = leanh::lean_ctor_get(v___y_9285_, 0);
                v_fileMap_9299_ = leanh::lean_ctor_get(v___y_9285_, 1);
                v_options_9300_ = leanh::lean_ctor_get(v___y_9285_, 2);
                v_currRecDepth_9301_ = leanh::lean_ctor_get(v___y_9285_, 3);
                v_maxRecDepth_9302_ = leanh::lean_ctor_get(v___y_9285_, 4);
                v_ref_9303_ = leanh::lean_ctor_get(v___y_9285_, 5);
                v_currNamespace_9304_ = leanh::lean_ctor_get(v___y_9285_, 6);
                v_openDecls_9305_ = leanh::lean_ctor_get(v___y_9285_, 7);
                v_initHeartbeats_9306_ = leanh::lean_ctor_get(v___y_9285_, 8);
                v_maxHeartbeats_9307_ = leanh::lean_ctor_get(v___y_9285_, 9);
                v_quotContext_9308_ = leanh::lean_ctor_get(v___y_9285_, 10);
                v_currMacroScope_9309_ = leanh::lean_ctor_get(v___y_9285_, 11);
                v_diag_9310_ = leanh::lean_ctor_get_uint8(
                    v___y_9285_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_9311_ = leanh::lean_ctor_get(v___y_9285_, 12);
                v_suppressElabErrors_9312_ = leanh::lean_ctor_get_uint8(
                    v___y_9285_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_9313_ = leanh::lean_ctor_get(v___y_9285_, 13);
                v___x_9319_ = leanh::lean_unsigned_to_nat(0);
                v___x_9320_ = lean_nat_dec_eq(v_maxRecDepth_9302_, v___x_9319_);
                if v___x_9320_ == 0 {
                    v___x_9321_ = lean_nat_dec_eq(v_currRecDepth_9301_, v_maxRecDepth_9302_);
                    if v___x_9321_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_x_9281_);
                        leanh::lean_inc(v_ref_9303_);
                        v___x_9322_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_9303_);
                        v___y_9289_ = v___x_9322_;
                        state = 1;
                        continue;
                    }
                } else {
                    state = 4;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_9289_) == 0 {
                    return v___y_9289_;
                } else {
                    v_a_9290_ = leanh::lean_ctor_get(v___y_9289_, 0);
                    v_isSharedCheck_9297_ = (!leanh::lean_is_exclusive(v___y_9289_)) as u8;
                    if v_isSharedCheck_9297_ == 0 {
                        v___x_9292_ = v___y_9289_;
                        v_isShared_9293_ = v_isSharedCheck_9297_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9290_);
                        leanh::lean_dec(v___y_9289_);
                        v___x_9292_ = leanh::lean_box(0);
                        v_isShared_9293_ = v_isSharedCheck_9297_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_9293_ == 0 {
                    v___x_9295_ = v___x_9292_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_9296_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9296_, 0, v_a_9290_);
                    v___x_9295_ = v_reuseFailAlloc_9296_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_9295_;
            }
            4 => {
                v___x_9315_ = leanh::lean_unsigned_to_nat(1);
                v___x_9316_ = lean_nat_add(v_currRecDepth_9301_, v___x_9315_);
                leanh::lean_inc_ref(v_inheritedTraceOptions_9313_);
                leanh::lean_inc(v_cancelTk_x3f_9311_);
                leanh::lean_inc(v_currMacroScope_9309_);
                leanh::lean_inc(v_quotContext_9308_);
                leanh::lean_inc(v_maxHeartbeats_9307_);
                leanh::lean_inc(v_initHeartbeats_9306_);
                leanh::lean_inc(v_openDecls_9305_);
                leanh::lean_inc(v_currNamespace_9304_);
                leanh::lean_inc(v_ref_9303_);
                leanh::lean_inc(v_maxRecDepth_9302_);
                leanh::lean_inc_ref(v_options_9300_);
                leanh::lean_inc_ref(v_fileMap_9299_);
                leanh::lean_inc_ref(v_fileName_9298_);
                v___x_9317_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_9317_, 0, v_fileName_9298_);
                leanh::lean_ctor_set(v___x_9317_, 1, v_fileMap_9299_);
                leanh::lean_ctor_set(v___x_9317_, 2, v_options_9300_);
                leanh::lean_ctor_set(v___x_9317_, 3, v___x_9316_);
                leanh::lean_ctor_set(v___x_9317_, 4, v_maxRecDepth_9302_);
                leanh::lean_ctor_set(v___x_9317_, 5, v_ref_9303_);
                leanh::lean_ctor_set(v___x_9317_, 6, v_currNamespace_9304_);
                leanh::lean_ctor_set(v___x_9317_, 7, v_openDecls_9305_);
                leanh::lean_ctor_set(v___x_9317_, 8, v_initHeartbeats_9306_);
                leanh::lean_ctor_set(v___x_9317_, 9, v_maxHeartbeats_9307_);
                leanh::lean_ctor_set(v___x_9317_, 10, v_quotContext_9308_);
                leanh::lean_ctor_set(v___x_9317_, 11, v_currMacroScope_9309_);
                leanh::lean_ctor_set(v___x_9317_, 12, v_cancelTk_x3f_9311_);
                leanh::lean_ctor_set(v___x_9317_, 13, v_inheritedTraceOptions_9313_);
                leanh::lean_ctor_set_uint8(
                    v___x_9317_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v_diag_9310_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_9317_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_9312_,
                );
                leanh::lean_inc(v___y_9286_);
                leanh::lean_inc(v___y_9284_);
                leanh::lean_inc_ref(v___y_9283_);
                leanh::lean_inc(v___y_9282_);
                v___x_9318_ = leanh::lean_apply_6(
                    v_x_9281_,
                    v___y_9282_,
                    v___y_9283_,
                    v___y_9284_,
                    v___x_9317_,
                    v___y_9286_,
                    leanh::lean_box(0),
                );
                v___y_9289_ = v___x_9318_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg___boxed(
    mut v_x_9323_: *mut leanh::LeanObject,
    mut v___y_9324_: *mut leanh::LeanObject,
    mut v___y_9325_: *mut leanh::LeanObject,
    mut v___y_9326_: *mut leanh::LeanObject,
    mut v___y_9327_: *mut leanh::LeanObject,
    mut v___y_9328_: *mut leanh::LeanObject,
    mut v___y_9329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9330_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_9323_, v___y_9324_, v___y_9325_, v___y_9326_, v___y_9327_, v___y_9328_);
    leanh::lean_dec(v___y_9328_);
    leanh::lean_dec_ref(v___y_9327_);
    leanh::lean_dec(v___y_9326_);
    leanh::lean_dec_ref(v___y_9325_);
    leanh::lean_dec(v___y_9324_);
    return v_res_9330_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(
    mut v_fvars_9331_: *mut leanh::LeanObject,
    mut v_pre_9332_: *mut leanh::LeanObject,
    mut v_post_9333_: *mut leanh::LeanObject,
    mut v_usedLetOnly_9334_: u8,
    mut v_skipConstInApp_9335_: u8,
    mut v_skipInstances_9336_: u8,
    mut v_body_9337_: *mut leanh::LeanObject,
    mut v_x_9338_: *mut leanh::LeanObject,
    mut v___y_9339_: *mut leanh::LeanObject,
    mut v___y_9340_: *mut leanh::LeanObject,
    mut v___y_9341_: *mut leanh::LeanObject,
    mut v___y_9342_: *mut leanh::LeanObject,
    mut v___y_9343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9345_ = lean_array_push(v_fvars_9331_, v_x_9338_);
    v___x_9346_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_9332_, v_post_9333_, v_usedLetOnly_9334_, v_skipConstInApp_9335_, v_skipInstances_9336_, v___x_9345_, v_body_9337_, v___y_9339_, v___y_9340_, v___y_9341_, v___y_9342_, v___y_9343_);
    return v___x_9346_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed(
    mut v_fvars_9347_: *mut leanh::LeanObject,
    mut v_pre_9348_: *mut leanh::LeanObject,
    mut v_post_9349_: *mut leanh::LeanObject,
    mut v_usedLetOnly_9350_: *mut leanh::LeanObject,
    mut v_skipConstInApp_9351_: *mut leanh::LeanObject,
    mut v_skipInstances_9352_: *mut leanh::LeanObject,
    mut v_body_9353_: *mut leanh::LeanObject,
    mut v_x_9354_: *mut leanh::LeanObject,
    mut v___y_9355_: *mut leanh::LeanObject,
    mut v___y_9356_: *mut leanh::LeanObject,
    mut v___y_9357_: *mut leanh::LeanObject,
    mut v___y_9358_: *mut leanh::LeanObject,
    mut v___y_9359_: *mut leanh::LeanObject,
    mut v___y_9360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_9361_: u8 = 0;
    let mut v_skipConstInApp_boxed_9362_: u8 = 0;
    let mut v_skipInstances_boxed_9363_: u8 = 0;
    let mut v_res_9364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_9361_ = (leanh::lean_unbox(v_usedLetOnly_9350_) as u8);
    v_skipConstInApp_boxed_9362_ = (leanh::lean_unbox(v_skipConstInApp_9351_) as u8);
    v_skipInstances_boxed_9363_ = (leanh::lean_unbox(v_skipInstances_9352_) as u8);
    v_res_9364_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_9347_, v_pre_9348_, v_post_9349_, v_usedLetOnly_boxed_9361_, v_skipConstInApp_boxed_9362_, v_skipInstances_boxed_9363_, v_body_9353_, v_x_9354_, v___y_9355_, v___y_9356_, v___y_9357_, v___y_9358_, v___y_9359_);
    leanh::lean_dec(v___y_9359_);
    leanh::lean_dec_ref(v___y_9358_);
    leanh::lean_dec(v___y_9357_);
    leanh::lean_dec_ref(v___y_9356_);
    leanh::lean_dec(v___y_9355_);
    return v_res_9364_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(
    mut v_pre_9365_: *mut leanh::LeanObject,
    mut v_post_9366_: *mut leanh::LeanObject,
    mut v_usedLetOnly_9367_: u8,
    mut v_skipConstInApp_9368_: u8,
    mut v_skipInstances_9369_: u8,
    mut v_e_9370_: *mut leanh::LeanObject,
    mut v_a_9371_: *mut leanh::LeanObject,
    mut v___y_9372_: *mut leanh::LeanObject,
    mut v___y_9373_: *mut leanh::LeanObject,
    mut v___y_9374_: *mut leanh::LeanObject,
    mut v___y_9375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9381_: u8 = 0;
    let mut v_e_9382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_9386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_9388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_9392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9396_: u8 = 0;
    let mut v_a_9397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9400_: u8 = 0;
    let mut v___x_9402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9404_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_post_9366_);
                leanh::lean_inc(v___y_9375_);
                leanh::lean_inc_ref(v___y_9374_);
                leanh::lean_inc(v___y_9373_);
                leanh::lean_inc_ref(v___y_9372_);
                leanh::lean_inc_ref(v_e_9370_);
                v___x_9377_ = leanh::lean_apply_6(
                    v_post_9366_,
                    v_e_9370_,
                    v___y_9372_,
                    v___y_9373_,
                    v___y_9374_,
                    v___y_9375_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_9377_) == 0 {
                    v_a_9378_ = leanh::lean_ctor_get(v___x_9377_, 0);
                    v_isSharedCheck_9396_ = (!leanh::lean_is_exclusive(v___x_9377_)) as u8;
                    if v_isSharedCheck_9396_ == 0 {
                        v___x_9380_ = v___x_9377_;
                        v_isShared_9381_ = v_isSharedCheck_9396_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9378_);
                        leanh::lean_dec(v___x_9377_);
                        v___x_9380_ = leanh::lean_box(0);
                        v_isShared_9381_ = v_isSharedCheck_9396_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_9370_);
                    leanh::lean_dec_ref(v_post_9366_);
                    leanh::lean_dec_ref(v_pre_9365_);
                    v_a_9397_ = leanh::lean_ctor_get(v___x_9377_, 0);
                    v_isSharedCheck_9404_ = (!leanh::lean_is_exclusive(v___x_9377_)) as u8;
                    if v_isSharedCheck_9404_ == 0 {
                        v___x_9399_ = v___x_9377_;
                        v_isShared_9400_ = v_isSharedCheck_9404_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9397_);
                        leanh::lean_dec(v___x_9377_);
                        v___x_9399_ = leanh::lean_box(0);
                        v_isShared_9400_ = v_isSharedCheck_9404_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => match leanh::lean_obj_tag(v_a_9378_) {
                0 => {
                    leanh::lean_dec_ref(v_e_9370_);
                    leanh::lean_dec_ref(v_post_9366_);
                    leanh::lean_dec_ref(v_pre_9365_);
                    v_e_9382_ = leanh::lean_ctor_get(v_a_9378_, 0);
                    leanh::lean_inc_ref(v_e_9382_);
                    leanh::lean_dec_ref_known(v_a_9378_, 1);
                    if v_isShared_9381_ == 0 {
                        leanh::lean_ctor_set(v___x_9380_, 0, v_e_9382_);
                        v___x_9384_ = v___x_9380_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_9385_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_9385_, 0, v_e_9382_);
                        v___x_9384_ = v_reuseFailAlloc_9385_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    leanh::lean_del_object(v___x_9380_);
                    leanh::lean_dec_ref(v_e_9370_);
                    v_e_9386_ = leanh::lean_ctor_get(v_a_9378_, 0);
                    leanh::lean_inc_ref(v_e_9386_);
                    leanh::lean_dec_ref_known(v_a_9378_, 1);
                    v___x_9387_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_9365_, v_post_9366_, v_usedLetOnly_9367_, v_skipConstInApp_9368_, v_skipInstances_9369_, v_e_9386_, v_a_9371_, v___y_9372_, v___y_9373_, v___y_9374_, v___y_9375_);
                    return v___x_9387_;
                }
                _ => {
                    leanh::lean_dec_ref(v_post_9366_);
                    leanh::lean_dec_ref(v_pre_9365_);
                    v_e_x3f_9388_ = leanh::lean_ctor_get(v_a_9378_, 0);
                    leanh::lean_inc(v_e_x3f_9388_);
                    leanh::lean_dec_ref_known(v_a_9378_, 1);
                    if leanh::lean_obj_tag(v_e_x3f_9388_) == 0 {
                        if v_isShared_9381_ == 0 {
                            leanh::lean_ctor_set(v___x_9380_, 0, v_e_9370_);
                            v___x_9390_ = v___x_9380_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_9391_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_9391_, 0, v_e_9370_);
                            v___x_9390_ = v_reuseFailAlloc_9391_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_9370_);
                        v_val_9392_ = leanh::lean_ctor_get(v_e_x3f_9388_, 0);
                        leanh::lean_inc(v_val_9392_);
                        leanh::lean_dec_ref_known(v_e_x3f_9388_, 1);
                        if v_isShared_9381_ == 0 {
                            leanh::lean_ctor_set(v___x_9380_, 0, v_val_9392_);
                            v___x_9394_ = v___x_9380_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_9395_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_9395_, 0, v_val_9392_);
                            v___x_9394_ = v_reuseFailAlloc_9395_;
                            state = 4;
                            continue;
                        }
                    }
                }
            },
            2 => {
                return v___x_9384_;
            }
            3 => {
                return v___x_9390_;
            }
            4 => {
                return v___x_9394_;
            }
            5 => {
                if v_isShared_9400_ == 0 {
                    v___x_9402_ = v___x_9399_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_9403_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9403_, 0, v_a_9397_);
                    v___x_9402_ = v_reuseFailAlloc_9403_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_9402_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(
    mut v_pre_9405_: *mut leanh::LeanObject,
    mut v_post_9406_: *mut leanh::LeanObject,
    mut v_usedLetOnly_9407_: u8,
    mut v_skipConstInApp_9408_: u8,
    mut v_skipInstances_9409_: u8,
    mut v_fvars_9410_: *mut leanh::LeanObject,
    mut v_e_9411_: *mut leanh::LeanObject,
    mut v_a_9412_: *mut leanh::LeanObject,
    mut v___y_9413_: *mut leanh::LeanObject,
    mut v___y_9414_: *mut leanh::LeanObject,
    mut v___y_9415_: *mut leanh::LeanObject,
    mut v___y_9416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_e_9411_) == 6 {
        let mut v_binderName_9418_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_9419_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_9420_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_9421_: u8 = 0;
        let mut v___x_9422_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_9423_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_binderName_9418_ = leanh::lean_ctor_get(v_e_9411_, 0);
        leanh::lean_inc(v_binderName_9418_);
        v_binderType_9419_ = leanh::lean_ctor_get(v_e_9411_, 1);
        leanh::lean_inc_ref(v_binderType_9419_);
        v_body_9420_ = leanh::lean_ctor_get(v_e_9411_, 2);
        leanh::lean_inc_ref(v_body_9420_);
        v_binderInfo_9421_ = leanh::lean_ctor_get_uint8(
            v_e_9411_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
        );
        leanh::lean_dec_ref_known(v_e_9411_, 3);
        v___x_9422_ = lean_expr_instantiate_rev(v_binderType_9419_, v_fvars_9410_);
        leanh::lean_dec_ref(v_binderType_9419_);
        leanh::lean_inc_ref(v_post_9406_);
        leanh::lean_inc_ref(v_pre_9405_);
        v___x_9423_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_9405_, v_post_9406_, v_usedLetOnly_9407_, v_skipConstInApp_9408_, v_skipInstances_9409_, v___x_9422_, v_a_9412_, v___y_9413_, v___y_9414_, v___y_9415_, v___y_9416_);
        if leanh::lean_obj_tag(v___x_9423_) == 0 {
            let mut v_a_9424_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_9425_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_9426_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_9427_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_9428_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_9429_: u8 = 0;
            let mut v___x_9430_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_9424_ = leanh::lean_ctor_get(v___x_9423_, 0);
            leanh::lean_inc(v_a_9424_);
            leanh::lean_dec_ref_known(v___x_9423_, 1);
            v___x_9425_ = leanh::lean_box((v_usedLetOnly_9407_) as usize);
            v___x_9426_ = leanh::lean_box((v_skipConstInApp_9408_) as usize);
            v___x_9427_ = leanh::lean_box((v_skipInstances_9409_) as usize);
            v___f_9428_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed as *mut core::ffi::c_void, 14, 7);
            leanh::lean_closure_set(v___f_9428_, 0, v_fvars_9410_);
            leanh::lean_closure_set(v___f_9428_, 1, v_pre_9405_);
            leanh::lean_closure_set(v___f_9428_, 2, v_post_9406_);
            leanh::lean_closure_set(v___f_9428_, 3, v___x_9425_);
            leanh::lean_closure_set(v___f_9428_, 4, v___x_9426_);
            leanh::lean_closure_set(v___f_9428_, 5, v___x_9427_);
            leanh::lean_closure_set(v___f_9428_, 6, v_body_9420_);
            v___x_9429_ = 0;
            v___x_9430_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_9418_, v_binderInfo_9421_, v_a_9424_, v___f_9428_, v___x_9429_, v_a_9412_, v___y_9413_, v___y_9414_, v___y_9415_, v___y_9416_);
            return v___x_9430_;
        } else {
            leanh::lean_dec_ref(v_body_9420_);
            leanh::lean_dec(v_binderName_9418_);
            leanh::lean_dec_ref(v_fvars_9410_);
            leanh::lean_dec_ref(v_post_9406_);
            leanh::lean_dec_ref(v_pre_9405_);
            return v___x_9423_;
        }
    } else {
        let mut v___x_9431_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_9432_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_9431_ = lean_expr_instantiate_rev(v_e_9411_, v_fvars_9410_);
        leanh::lean_dec_ref(v_e_9411_);
        leanh::lean_inc_ref(v_post_9406_);
        leanh::lean_inc_ref(v_pre_9405_);
        v___x_9432_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_9405_, v_post_9406_, v_usedLetOnly_9407_, v_skipConstInApp_9408_, v_skipInstances_9409_, v___x_9431_, v_a_9412_, v___y_9413_, v___y_9414_, v___y_9415_, v___y_9416_);
        if leanh::lean_obj_tag(v___x_9432_) == 0 {
            let mut v_a_9433_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_9434_: u8 = 0;
            let mut v___x_9435_: u8 = 0;
            let mut v___x_9436_: u8 = 0;
            let mut v___x_9437_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_9433_ = leanh::lean_ctor_get(v___x_9432_, 0);
            leanh::lean_inc(v_a_9433_);
            leanh::lean_dec_ref_known(v___x_9432_, 1);
            v___x_9434_ = 0;
            v___x_9435_ = 1;
            v___x_9436_ = 1;
            v___x_9437_ = l_Lean_Meta_mkLambdaFVars(
                v_fvars_9410_,
                v_a_9433_,
                v___x_9434_,
                v_usedLetOnly_9407_,
                v___x_9434_,
                v___x_9435_,
                v___x_9436_,
                v___y_9413_,
                v___y_9414_,
                v___y_9415_,
                v___y_9416_,
            );
            leanh::lean_dec_ref(v_fvars_9410_);
            if leanh::lean_obj_tag(v___x_9437_) == 0 {
                let mut v_a_9438_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_9439_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_a_9438_ = leanh::lean_ctor_get(v___x_9437_, 0);
                leanh::lean_inc(v_a_9438_);
                leanh::lean_dec_ref_known(v___x_9437_, 1);
                v___x_9439_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_9405_, v_post_9406_, v_usedLetOnly_9407_, v_skipConstInApp_9408_, v_skipInstances_9409_, v_a_9438_, v_a_9412_, v___y_9413_, v___y_9414_, v___y_9415_, v___y_9416_);
                return v___x_9439_;
            } else {
                leanh::lean_dec_ref(v_post_9406_);
                leanh::lean_dec_ref(v_pre_9405_);
                return v___x_9437_;
            }
        } else {
            leanh::lean_dec_ref(v_fvars_9410_);
            leanh::lean_dec_ref(v_post_9406_);
            leanh::lean_dec_ref(v_pre_9405_);
            return v___x_9432_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(
    mut v_fvars_9440_: *mut leanh::LeanObject,
    mut v_pre_9441_: *mut leanh::LeanObject,
    mut v_post_9442_: *mut leanh::LeanObject,
    mut v_usedLetOnly_9443_: u8,
    mut v_skipConstInApp_9444_: u8,
    mut v_skipInstances_9445_: u8,
    mut v_body_9446_: *mut leanh::LeanObject,
    mut v_x_9447_: *mut leanh::LeanObject,
    mut v___y_9448_: *mut leanh::LeanObject,
    mut v___y_9449_: *mut leanh::LeanObject,
    mut v___y_9450_: *mut leanh::LeanObject,
    mut v___y_9451_: *mut leanh::LeanObject,
    mut v___y_9452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9454_ = lean_array_push(v_fvars_9440_, v_x_9447_);
    v___x_9455_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_9441_, v_post_9442_, v_usedLetOnly_9443_, v_skipConstInApp_9444_, v_skipInstances_9445_, v___x_9454_, v_body_9446_, v___y_9448_, v___y_9449_, v___y_9450_, v___y_9451_, v___y_9452_);
    return v___x_9455_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed(
    mut v_fvars_9456_: *mut leanh::LeanObject,
    mut v_pre_9457_: *mut leanh::LeanObject,
    mut v_post_9458_: *mut leanh::LeanObject,
    mut v_usedLetOnly_9459_: *mut leanh::LeanObject,
    mut v_skipConstInApp_9460_: *mut leanh::LeanObject,
    mut v_skipInstances_9461_: *mut leanh::LeanObject,
    mut v_body_9462_: *mut leanh::LeanObject,
    mut v_x_9463_: *mut leanh::LeanObject,
    mut v___y_9464_: *mut leanh::LeanObject,
    mut v___y_9465_: *mut leanh::LeanObject,
    mut v___y_9466_: *mut leanh::LeanObject,
    mut v___y_9467_: *mut leanh::LeanObject,
    mut v___y_9468_: *mut leanh::LeanObject,
    mut v___y_9469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_9470_: u8 = 0;
    let mut v_skipConstInApp_boxed_9471_: u8 = 0;
    let mut v_skipInstances_boxed_9472_: u8 = 0;
    let mut v_res_9473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_9470_ = (leanh::lean_unbox(v_usedLetOnly_9459_) as u8);
    v_skipConstInApp_boxed_9471_ = (leanh::lean_unbox(v_skipConstInApp_9460_) as u8);
    v_skipInstances_boxed_9472_ = (leanh::lean_unbox(v_skipInstances_9461_) as u8);
    v_res_9473_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_9456_, v_pre_9457_, v_post_9458_, v_usedLetOnly_boxed_9470_, v_skipConstInApp_boxed_9471_, v_skipInstances_boxed_9472_, v_body_9462_, v_x_9463_, v___y_9464_, v___y_9465_, v___y_9466_, v___y_9467_, v___y_9468_);
    leanh::lean_dec(v___y_9468_);
    leanh::lean_dec_ref(v___y_9467_);
    leanh::lean_dec(v___y_9466_);
    leanh::lean_dec_ref(v___y_9465_);
    leanh::lean_dec(v___y_9464_);
    return v_res_9473_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(
    mut v_pre_9474_: *mut leanh::LeanObject,
    mut v_post_9475_: *mut leanh::LeanObject,
    mut v_usedLetOnly_9476_: u8,
    mut v_skipConstInApp_9477_: u8,
    mut v_skipInstances_9478_: u8,
    mut v_fvars_9479_: *mut leanh::LeanObject,
    mut v_e_9480_: *mut leanh::LeanObject,
    mut v_a_9481_: *mut leanh::LeanObject,
    mut v___y_9482_: *mut leanh::LeanObject,
    mut v___y_9483_: *mut leanh::LeanObject,
    mut v___y_9484_: *mut leanh::LeanObject,
    mut v___y_9485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_e_9480_) == 8 {
        let mut v_declName_9487_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_type_9488_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_9489_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_9490_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_nondep_9491_: u8 = 0;
        let mut v___x_9492_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_9493_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_declName_9487_ = leanh::lean_ctor_get(v_e_9480_, 0);
        leanh::lean_inc(v_declName_9487_);
        v_type_9488_ = leanh::lean_ctor_get(v_e_9480_, 1);
        leanh::lean_inc_ref(v_type_9488_);
        v_value_9489_ = leanh::lean_ctor_get(v_e_9480_, 2);
        leanh::lean_inc_ref(v_value_9489_);
        v_body_9490_ = leanh::lean_ctor_get(v_e_9480_, 3);
        leanh::lean_inc_ref(v_body_9490_);
        v_nondep_9491_ = leanh::lean_ctor_get_uint8(
            v_e_9480_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8) as u32,
        );
        leanh::lean_dec_ref_known(v_e_9480_, 4);
        v___x_9492_ = lean_expr_instantiate_rev(v_type_9488_, v_fvars_9479_);
        leanh::lean_dec_ref(v_type_9488_);
        leanh::lean_inc_ref(v_post_9475_);
        leanh::lean_inc_ref(v_pre_9474_);
        v___x_9493_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_9474_, v_post_9475_, v_usedLetOnly_9476_, v_skipConstInApp_9477_, v_skipInstances_9478_, v___x_9492_, v_a_9481_, v___y_9482_, v___y_9483_, v___y_9484_, v___y_9485_);
        if leanh::lean_obj_tag(v___x_9493_) == 0 {
            let mut v_a_9494_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_9495_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_9496_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_9494_ = leanh::lean_ctor_get(v___x_9493_, 0);
            leanh::lean_inc(v_a_9494_);
            leanh::lean_dec_ref_known(v___x_9493_, 1);
            v___x_9495_ = lean_expr_instantiate_rev(v_value_9489_, v_fvars_9479_);
            leanh::lean_dec_ref(v_value_9489_);
            leanh::lean_inc_ref(v_post_9475_);
            leanh::lean_inc_ref(v_pre_9474_);
            v___x_9496_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_9474_, v_post_9475_, v_usedLetOnly_9476_, v_skipConstInApp_9477_, v_skipInstances_9478_, v___x_9495_, v_a_9481_, v___y_9482_, v___y_9483_, v___y_9484_, v___y_9485_);
            if leanh::lean_obj_tag(v___x_9496_) == 0 {
                let mut v_a_9497_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_9498_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_9499_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_9500_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_9501_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_9502_: u8 = 0;
                let mut v___x_9503_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_a_9497_ = leanh::lean_ctor_get(v___x_9496_, 0);
                leanh::lean_inc(v_a_9497_);
                leanh::lean_dec_ref_known(v___x_9496_, 1);
                v___x_9498_ = leanh::lean_box((v_usedLetOnly_9476_) as usize);
                v___x_9499_ = leanh::lean_box((v_skipConstInApp_9477_) as usize);
                v___x_9500_ = leanh::lean_box((v_skipInstances_9478_) as usize);
                v___f_9501_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed as *mut core::ffi::c_void, 14, 7);
                leanh::lean_closure_set(v___f_9501_, 0, v_fvars_9479_);
                leanh::lean_closure_set(v___f_9501_, 1, v_pre_9474_);
                leanh::lean_closure_set(v___f_9501_, 2, v_post_9475_);
                leanh::lean_closure_set(v___f_9501_, 3, v___x_9498_);
                leanh::lean_closure_set(v___f_9501_, 4, v___x_9499_);
                leanh::lean_closure_set(v___f_9501_, 5, v___x_9500_);
                leanh::lean_closure_set(v___f_9501_, 6, v_body_9490_);
                v___x_9502_ = 0;
                v___x_9503_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_declName_9487_, v_a_9494_, v_a_9497_, v___f_9501_, v_nondep_9491_, v___x_9502_, v_a_9481_, v___y_9482_, v___y_9483_, v___y_9484_, v___y_9485_);
                return v___x_9503_;
            } else {
                leanh::lean_dec(v_a_9494_);
                leanh::lean_dec_ref(v_body_9490_);
                leanh::lean_dec(v_declName_9487_);
                leanh::lean_dec_ref(v_fvars_9479_);
                leanh::lean_dec_ref(v_post_9475_);
                leanh::lean_dec_ref(v_pre_9474_);
                return v___x_9496_;
            }
        } else {
            leanh::lean_dec_ref(v_body_9490_);
            leanh::lean_dec_ref(v_value_9489_);
            leanh::lean_dec(v_declName_9487_);
            leanh::lean_dec_ref(v_fvars_9479_);
            leanh::lean_dec_ref(v_post_9475_);
            leanh::lean_dec_ref(v_pre_9474_);
            return v___x_9493_;
        }
    } else {
        let mut v___x_9504_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_9505_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_9504_ = lean_expr_instantiate_rev(v_e_9480_, v_fvars_9479_);
        leanh::lean_dec_ref(v_e_9480_);
        leanh::lean_inc_ref(v_post_9475_);
        leanh::lean_inc_ref(v_pre_9474_);
        v___x_9505_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_9474_, v_post_9475_, v_usedLetOnly_9476_, v_skipConstInApp_9477_, v_skipInstances_9478_, v___x_9504_, v_a_9481_, v___y_9482_, v___y_9483_, v___y_9484_, v___y_9485_);
        if leanh::lean_obj_tag(v___x_9505_) == 0 {
            let mut v_a_9506_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_9507_: u8 = 0;
            let mut v___x_9508_: u8 = 0;
            let mut v___x_9509_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_9506_ = leanh::lean_ctor_get(v___x_9505_, 0);
            leanh::lean_inc(v_a_9506_);
            leanh::lean_dec_ref_known(v___x_9505_, 1);
            v___x_9507_ = 0;
            v___x_9508_ = 1;
            v___x_9509_ = l_Lean_Meta_mkLetFVars(
                v_fvars_9479_,
                v_a_9506_,
                v_usedLetOnly_9476_,
                v___x_9507_,
                v___x_9508_,
                v___y_9482_,
                v___y_9483_,
                v___y_9484_,
                v___y_9485_,
            );
            leanh::lean_dec_ref(v_fvars_9479_);
            if leanh::lean_obj_tag(v___x_9509_) == 0 {
                let mut v_a_9510_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_9511_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_a_9510_ = leanh::lean_ctor_get(v___x_9509_, 0);
                leanh::lean_inc(v_a_9510_);
                leanh::lean_dec_ref_known(v___x_9509_, 1);
                v___x_9511_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_9474_, v_post_9475_, v_usedLetOnly_9476_, v_skipConstInApp_9477_, v_skipInstances_9478_, v_a_9510_, v_a_9481_, v___y_9482_, v___y_9483_, v___y_9484_, v___y_9485_);
                return v___x_9511_;
            } else {
                leanh::lean_dec_ref(v_post_9475_);
                leanh::lean_dec_ref(v_pre_9474_);
                return v___x_9509_;
            }
        } else {
            leanh::lean_dec_ref(v_fvars_9479_);
            leanh::lean_dec_ref(v_post_9475_);
            leanh::lean_dec_ref(v_pre_9474_);
            return v___x_9505_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(
    mut v_pre_9512_: *mut leanh::LeanObject,
    mut v_post_9513_: *mut leanh::LeanObject,
    mut v_usedLetOnly_9514_: u8,
    mut v_skipConstInApp_9515_: u8,
    mut v_skipInstances_9516_: u8,
    mut v_sz_9517_: usize,
    mut v_i_9518_: usize,
    mut v_bs_9519_: *mut leanh::LeanObject,
    mut v___y_9520_: *mut leanh::LeanObject,
    mut v___y_9521_: *mut leanh::LeanObject,
    mut v___y_9522_: *mut leanh::LeanObject,
    mut v___y_9523_: *mut leanh::LeanObject,
    mut v___y_9524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9526_: u8 = 0;
    let mut v___x_9527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_9528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_9532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9533_: usize = 0;
    let mut v___x_9534_: usize = 0;
    let mut v___x_9535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9540_: u8 = 0;
    let mut v___x_9542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9544_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9526_ = lean_usize_dec_lt(v_i_9518_, v_sz_9517_);
                if v___x_9526_ == 0 {
                    leanh::lean_dec_ref(v_post_9513_);
                    leanh::lean_dec_ref(v_pre_9512_);
                    v___x_9527_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_9527_, 0, v_bs_9519_);
                    return v___x_9527_;
                } else {
                    v_v_9528_ = lean_array_uget_borrowed(v_bs_9519_, v_i_9518_);
                    leanh::lean_inc(v_v_9528_);
                    leanh::lean_inc_ref(v_post_9513_);
                    leanh::lean_inc_ref(v_pre_9512_);
                    v___x_9529_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_9512_, v_post_9513_, v_usedLetOnly_9514_, v_skipConstInApp_9515_, v_skipInstances_9516_, v_v_9528_, v___y_9520_, v___y_9521_, v___y_9522_, v___y_9523_, v___y_9524_);
                    if leanh::lean_obj_tag(v___x_9529_) == 0 {
                        v_a_9530_ = leanh::lean_ctor_get(v___x_9529_, 0);
                        leanh::lean_inc(v_a_9530_);
                        leanh::lean_dec_ref_known(v___x_9529_, 1);
                        v___x_9531_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_9532_ = lean_array_uset(v_bs_9519_, v_i_9518_, v___x_9531_);
                        v___x_9533_ = 1usize;
                        v___x_9534_ = lean_usize_add(v_i_9518_, v___x_9533_);
                        v___x_9535_ = lean_array_uset(v_bs_x27_9532_, v_i_9518_, v_a_9530_);
                        v_i_9518_ = v___x_9534_;
                        v_bs_9519_ = v___x_9535_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_9519_);
                        leanh::lean_dec_ref(v_post_9513_);
                        leanh::lean_dec_ref(v_pre_9512_);
                        v_a_9537_ = leanh::lean_ctor_get(v___x_9529_, 0);
                        v_isSharedCheck_9544_ =
                            (!leanh::lean_is_exclusive(v___x_9529_)) as u8;
                        if v_isSharedCheck_9544_ == 0 {
                            v___x_9539_ = v___x_9529_;
                            v_isShared_9540_ = v_isSharedCheck_9544_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_9537_);
                            leanh::lean_dec(v___x_9529_);
                            v___x_9539_ = leanh::lean_box(0);
                            v_isShared_9540_ = v_isSharedCheck_9544_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_9540_ == 0 {
                    v___x_9542_ = v___x_9539_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9543_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9543_, 0, v_a_9537_);
                    v___x_9542_ = v_reuseFailAlloc_9543_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9542_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(
    mut v_pre_9545_: *mut leanh::LeanObject,
    mut v_post_9546_: *mut leanh::LeanObject,
    mut v_usedLetOnly_9547_: u8,
    mut v_skipConstInApp_9548_: u8,
    mut v_skipInstances_9549_: u8,
    mut v___x_9550_: *mut leanh::LeanObject,
    mut v___y_9551_: *mut leanh::LeanObject,
    mut v_b_9552_: *mut leanh::LeanObject,
    mut v_a_9553_: *mut leanh::LeanObject,
    mut v___y_9554_: *mut leanh::LeanObject,
    mut v___y_9555_: *mut leanh::LeanObject,
    mut v___y_9556_: *mut leanh::LeanObject,
    mut v___y_9557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9563_: u8 = 0;
    let mut v___x_9564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9569_: u8 = 0;
    let mut v_a_9570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9573_: u8 = 0;
    let mut v___x_9575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9577_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9559_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_9545_, v_post_9546_, v_usedLetOnly_9547_, v_skipConstInApp_9548_, v_skipInstances_9549_, v___x_9550_, v___y_9551_, v___y_9554_, v___y_9555_, v___y_9556_, v___y_9557_);
                if leanh::lean_obj_tag(v___x_9559_) == 0 {
                    v_a_9560_ = leanh::lean_ctor_get(v___x_9559_, 0);
                    v_isSharedCheck_9569_ = (!leanh::lean_is_exclusive(v___x_9559_)) as u8;
                    if v_isSharedCheck_9569_ == 0 {
                        v___x_9562_ = v___x_9559_;
                        v_isShared_9563_ = v_isSharedCheck_9569_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9560_);
                        leanh::lean_dec(v___x_9559_);
                        v___x_9562_ = leanh::lean_box(0);
                        v_isShared_9563_ = v_isSharedCheck_9569_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_b_9552_);
                    v_a_9570_ = leanh::lean_ctor_get(v___x_9559_, 0);
                    v_isSharedCheck_9577_ = (!leanh::lean_is_exclusive(v___x_9559_)) as u8;
                    if v_isSharedCheck_9577_ == 0 {
                        v___x_9572_ = v___x_9559_;
                        v_isShared_9573_ = v_isSharedCheck_9577_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9570_);
                        leanh::lean_dec(v___x_9559_);
                        v___x_9572_ = leanh::lean_box(0);
                        v_isShared_9573_ = v_isSharedCheck_9577_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_9564_ = lean_array_fset(v_b_9552_, v_a_9553_, v_a_9560_);
                v___x_9565_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_9565_, 0, v___x_9564_);
                if v_isShared_9563_ == 0 {
                    leanh::lean_ctor_set(v___x_9562_, 0, v___x_9565_);
                    v___x_9567_ = v___x_9562_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9568_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9568_, 0, v___x_9565_);
                    v___x_9567_ = v_reuseFailAlloc_9568_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9567_;
            }
            3 => {
                if v_isShared_9573_ == 0 {
                    v___x_9575_ = v___x_9572_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9576_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9576_, 0, v_a_9570_);
                    v___x_9575_ = v_reuseFailAlloc_9576_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9575_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(
    mut v_pre_9578_: *mut leanh::LeanObject,
    mut v_post_9579_: *mut leanh::LeanObject,
    mut v_usedLetOnly_9580_: *mut leanh::LeanObject,
    mut v_skipConstInApp_9581_: *mut leanh::LeanObject,
    mut v_skipInstances_9582_: *mut leanh::LeanObject,
    mut v___x_9583_: *mut leanh::LeanObject,
    mut v___y_9584_: *mut leanh::LeanObject,
    mut v_b_9585_: *mut leanh::LeanObject,
    mut v_a_9586_: *mut leanh::LeanObject,
    mut v___y_9587_: *mut leanh::LeanObject,
    mut v___y_9588_: *mut leanh::LeanObject,
    mut v___y_9589_: *mut leanh::LeanObject,
    mut v___y_9590_: *mut leanh::LeanObject,
    mut v___y_9591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_9592_: u8 = 0;
    let mut v_skipConstInApp_boxed_9593_: u8 = 0;
    let mut v_skipInstances_boxed_9594_: u8 = 0;
    let mut v_res_9595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_9592_ = (leanh::lean_unbox(v_usedLetOnly_9580_) as u8);
    v_skipConstInApp_boxed_9593_ = (leanh::lean_unbox(v_skipConstInApp_9581_) as u8);
    v_skipInstances_boxed_9594_ = (leanh::lean_unbox(v_skipInstances_9582_) as u8);
    v_res_9595_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_9578_, v_post_9579_, v_usedLetOnly_boxed_9592_, v_skipConstInApp_boxed_9593_, v_skipInstances_boxed_9594_, v___x_9583_, v___y_9584_, v_b_9585_, v_a_9586_, v___y_9587_, v___y_9588_, v___y_9589_, v___y_9590_);
    leanh::lean_dec(v___y_9590_);
    leanh::lean_dec_ref(v___y_9589_);
    leanh::lean_dec(v___y_9588_);
    leanh::lean_dec_ref(v___y_9587_);
    leanh::lean_dec(v_a_9586_);
    leanh::lean_dec(v___y_9584_);
    return v_res_9595_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(
    mut v_upperBound_9596_: *mut leanh::LeanObject,
    mut v___x_9597_: *mut leanh::LeanObject,
    mut v_pre_9598_: *mut leanh::LeanObject,
    mut v_post_9599_: *mut leanh::LeanObject,
    mut v_usedLetOnly_9600_: u8,
    mut v_skipConstInApp_9601_: u8,
    mut v_skipInstances_9602_: u8,
    mut v_a_9603_: *mut leanh::LeanObject,
    mut v_b_9604_: *mut leanh::LeanObject,
    mut v___y_9605_: *mut leanh::LeanObject,
    mut v___y_9606_: *mut leanh::LeanObject,
    mut v___y_9607_: *mut leanh::LeanObject,
    mut v___y_9608_: *mut leanh::LeanObject,
    mut v___y_9609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_9612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9617_: u8 = 0;
    let mut v_a_9618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9626_: u8 = 0;
    let mut v_a_9627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9630_: u8 = 0;
    let mut v___x_9632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9634_: u8 = 0;
    let mut v___x_9635_: u8 = 0;
    let mut v___x_9636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9639_: u8 = 0;
    let mut v___x_9640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_9643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInstance_9645_: u8 = 0;
    let mut v___x_9646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_9649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_9651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9635_ = lean_nat_dec_lt(v_a_9603_, v_upperBound_9596_);
                if v___x_9635_ == 0 {
                    leanh::lean_dec(v_a_9603_);
                    leanh::lean_dec_ref(v_post_9599_);
                    leanh::lean_dec_ref(v_pre_9598_);
                    v___x_9636_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_9636_, 0, v_b_9604_);
                    return v___x_9636_;
                } else {
                    v___x_9637_ = lean_array_fget_borrowed(v_b_9604_, v_a_9603_);
                    v___x_9638_ = lean_array_get_size(v___x_9597_);
                    v___x_9639_ = lean_nat_dec_lt(v_a_9603_, v___x_9638_);
                    if v___x_9639_ == 0 {
                        leanh::lean_inc(v___x_9637_);
                        v___x_9640_ = leanh::lean_box((v_usedLetOnly_9600_) as usize);
                        v___x_9641_ = leanh::lean_box((v_skipConstInApp_9601_) as usize);
                        v___x_9642_ = leanh::lean_box((v_skipInstances_9602_) as usize);
                        leanh::lean_inc(v_a_9603_);
                        leanh::lean_inc(v___y_9605_);
                        leanh::lean_inc_ref(v_post_9599_);
                        leanh::lean_inc_ref(v_pre_9598_);
                        v___f_9643_ = leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 9);
                        leanh::lean_closure_set(v___f_9643_, 0, v_pre_9598_);
                        leanh::lean_closure_set(v___f_9643_, 1, v_post_9599_);
                        leanh::lean_closure_set(v___f_9643_, 2, v___x_9640_);
                        leanh::lean_closure_set(v___f_9643_, 3, v___x_9641_);
                        leanh::lean_closure_set(v___f_9643_, 4, v___x_9642_);
                        leanh::lean_closure_set(v___f_9643_, 5, v___x_9637_);
                        leanh::lean_closure_set(v___f_9643_, 6, v___y_9605_);
                        leanh::lean_closure_set(v___f_9643_, 7, v_b_9604_);
                        leanh::lean_closure_set(v___f_9643_, 8, v_a_9603_);
                        v___y_9612_ = v___f_9643_;
                        state = 1;
                        continue;
                    } else {
                        v___x_9644_ = lean_array_fget_borrowed(v___x_9597_, v_a_9603_);
                        v_isInstance_9645_ = leanh::lean_ctor_get_uint8(
                            v___x_9644_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 4) as u32,
                        );
                        if v_isInstance_9645_ == 0 {
                            leanh::lean_inc(v___x_9637_);
                            v___x_9646_ = leanh::lean_box((v_usedLetOnly_9600_) as usize);
                            v___x_9647_ = leanh::lean_box((v_skipConstInApp_9601_) as usize);
                            v___x_9648_ = leanh::lean_box((v_skipInstances_9602_) as usize);
                            leanh::lean_inc(v_a_9603_);
                            leanh::lean_inc(v___y_9605_);
                            leanh::lean_inc_ref(v_post_9599_);
                            leanh::lean_inc_ref(v_pre_9598_);
                            v___f_9649_ = leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 9);
                            leanh::lean_closure_set(v___f_9649_, 0, v_pre_9598_);
                            leanh::lean_closure_set(v___f_9649_, 1, v_post_9599_);
                            leanh::lean_closure_set(v___f_9649_, 2, v___x_9646_);
                            leanh::lean_closure_set(v___f_9649_, 3, v___x_9647_);
                            leanh::lean_closure_set(v___f_9649_, 4, v___x_9648_);
                            leanh::lean_closure_set(v___f_9649_, 5, v___x_9637_);
                            leanh::lean_closure_set(v___f_9649_, 6, v___y_9605_);
                            leanh::lean_closure_set(v___f_9649_, 7, v_b_9604_);
                            leanh::lean_closure_set(v___f_9649_, 8, v_a_9603_);
                            v___y_9612_ = v___f_9649_;
                            state = 1;
                            continue;
                        } else {
                            v___x_9650_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_9650_, 0, v_b_9604_);
                            v___f_9651_ = leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed as *mut core::ffi::c_void, 6, 1);
                            leanh::lean_closure_set(v___f_9651_, 0, v___x_9650_);
                            v___y_9612_ = v___f_9651_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc(v___y_9609_);
                leanh::lean_inc_ref(v___y_9608_);
                leanh::lean_inc(v___y_9607_);
                leanh::lean_inc_ref(v___y_9606_);
                v___x_9613_ = leanh::lean_apply_5(
                    v___y_9612_,
                    v___y_9606_,
                    v___y_9607_,
                    v___y_9608_,
                    v___y_9609_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_9613_) == 0 {
                    v_a_9614_ = leanh::lean_ctor_get(v___x_9613_, 0);
                    v_isSharedCheck_9626_ = (!leanh::lean_is_exclusive(v___x_9613_)) as u8;
                    if v_isSharedCheck_9626_ == 0 {
                        v___x_9616_ = v___x_9613_;
                        v_isShared_9617_ = v_isSharedCheck_9626_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9614_);
                        leanh::lean_dec(v___x_9613_);
                        v___x_9616_ = leanh::lean_box(0);
                        v_isShared_9617_ = v_isSharedCheck_9626_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_9603_);
                    leanh::lean_dec_ref(v_post_9599_);
                    leanh::lean_dec_ref(v_pre_9598_);
                    v_a_9627_ = leanh::lean_ctor_get(v___x_9613_, 0);
                    v_isSharedCheck_9634_ = (!leanh::lean_is_exclusive(v___x_9613_)) as u8;
                    if v_isSharedCheck_9634_ == 0 {
                        v___x_9629_ = v___x_9613_;
                        v_isShared_9630_ = v_isSharedCheck_9634_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9627_);
                        leanh::lean_dec(v___x_9613_);
                        v___x_9629_ = leanh::lean_box(0);
                        v_isShared_9630_ = v_isSharedCheck_9634_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_9614_) == 0 {
                    leanh::lean_dec(v_a_9603_);
                    leanh::lean_dec_ref(v_post_9599_);
                    leanh::lean_dec_ref(v_pre_9598_);
                    v_a_9618_ = leanh::lean_ctor_get(v_a_9614_, 0);
                    leanh::lean_inc(v_a_9618_);
                    leanh::lean_dec_ref_known(v_a_9614_, 1);
                    if v_isShared_9617_ == 0 {
                        leanh::lean_ctor_set(v___x_9616_, 0, v_a_9618_);
                        v___x_9620_ = v___x_9616_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_9621_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_9621_, 0, v_a_9618_);
                        v___x_9620_ = v_reuseFailAlloc_9621_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_9616_);
                    v_a_9622_ = leanh::lean_ctor_get(v_a_9614_, 0);
                    leanh::lean_inc(v_a_9622_);
                    leanh::lean_dec_ref_known(v_a_9614_, 1);
                    v___x_9623_ = leanh::lean_unsigned_to_nat(1);
                    v___x_9624_ = lean_nat_add(v_a_9603_, v___x_9623_);
                    leanh::lean_dec(v_a_9603_);
                    v_a_9603_ = v___x_9624_;
                    v_b_9604_ = v_a_9622_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_9620_;
            }
            4 => {
                if v_isShared_9630_ == 0 {
                    v___x_9632_ = v___x_9629_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_9633_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9633_, 0, v_a_9627_);
                    v___x_9632_ = v_reuseFailAlloc_9633_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_9632_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(
    mut v_skipInstances_9652_: u8,
    mut v_pre_9653_: *mut leanh::LeanObject,
    mut v_post_9654_: *mut leanh::LeanObject,
    mut v_usedLetOnly_9655_: u8,
    mut v_skipConstInApp_9656_: u8,
    mut v_x_9657_: *mut leanh::LeanObject,
    mut v_x_9658_: *mut leanh::LeanObject,
    mut v_x_9659_: *mut leanh::LeanObject,
    mut v___y_9660_: *mut leanh::LeanObject,
    mut v___y_9661_: *mut leanh::LeanObject,
    mut v___y_9662_: *mut leanh::LeanObject,
    mut v___y_9663_: *mut leanh::LeanObject,
    mut v___y_9664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_f_9667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_9668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_9669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_9670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_9671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_9672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_9673_: usize = 0;
    let mut v___x_9674_: usize = 0;
    let mut v___x_9675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9682_: u8 = 0;
    let mut v___x_9684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9686_: u8 = 0;
    let mut v___x_9687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramInfo_9690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9699_: u8 = 0;
    let mut v___x_9701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9703_: u8 = 0;
    let mut v_a_9704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9707_: u8 = 0;
    let mut v___x_9709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9711_: u8 = 0;
    let mut v___x_9713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_9715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_9716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9721_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_9657_) == 5 {
                    v_fn_9715_ = leanh::lean_ctor_get(v_x_9657_, 0);
                    leanh::lean_inc_ref(v_fn_9715_);
                    v_arg_9716_ = leanh::lean_ctor_get(v_x_9657_, 1);
                    leanh::lean_inc_ref(v_arg_9716_);
                    leanh::lean_dec_ref_known(v_x_9657_, 2);
                    v___x_9717_ = lean_array_set(v_x_9658_, v_x_9659_, v_arg_9716_);
                    v___x_9718_ = leanh::lean_unsigned_to_nat(1);
                    v___x_9719_ = lean_nat_sub(v_x_9659_, v___x_9718_);
                    leanh::lean_dec(v_x_9659_);
                    v_x_9657_ = v_fn_9715_;
                    v_x_9658_ = v___x_9717_;
                    v_x_9659_ = v___x_9719_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_x_9659_);
                    if v_skipConstInApp_9656_ == 0 {
                        state = 8;
                        continue;
                    } else {
                        v___x_9721_ = l_Lean_Expr_isConst(v_x_9657_);
                        if v___x_9721_ == 0 {
                            state = 8;
                            continue;
                        } else {
                            v_f_9667_ = v_x_9657_;
                            v___y_9668_ = v___y_9660_;
                            v___y_9669_ = v___y_9661_;
                            v___y_9670_ = v___y_9662_;
                            v___y_9671_ = v___y_9663_;
                            v___y_9672_ = v___y_9664_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_skipInstances_9652_ == 0 {
                    v_sz_9673_ = lean_array_size(v_x_9658_);
                    v___x_9674_ = 0usize;
                    leanh::lean_inc_ref(v_post_9654_);
                    leanh::lean_inc_ref(v_pre_9653_);
                    v___x_9675_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_9653_, v_post_9654_, v_usedLetOnly_9655_, v_skipConstInApp_9656_, v_skipInstances_9652_, v_sz_9673_, v___x_9674_, v_x_9658_, v___y_9668_, v___y_9669_, v___y_9670_, v___y_9671_, v___y_9672_);
                    if leanh::lean_obj_tag(v___x_9675_) == 0 {
                        v_a_9676_ = leanh::lean_ctor_get(v___x_9675_, 0);
                        leanh::lean_inc(v_a_9676_);
                        leanh::lean_dec_ref_known(v___x_9675_, 1);
                        v___x_9677_ = l_Lean_mkAppN(v_f_9667_, v_a_9676_);
                        leanh::lean_dec(v_a_9676_);
                        v___x_9678_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_9653_, v_post_9654_, v_usedLetOnly_9655_, v_skipConstInApp_9656_, v_skipInstances_9652_, v___x_9677_, v___y_9668_, v___y_9669_, v___y_9670_, v___y_9671_, v___y_9672_);
                        return v___x_9678_;
                    } else {
                        leanh::lean_dec_ref(v_f_9667_);
                        leanh::lean_dec_ref(v_post_9654_);
                        leanh::lean_dec_ref(v_pre_9653_);
                        v_a_9679_ = leanh::lean_ctor_get(v___x_9675_, 0);
                        v_isSharedCheck_9686_ =
                            (!leanh::lean_is_exclusive(v___x_9675_)) as u8;
                        if v_isSharedCheck_9686_ == 0 {
                            v___x_9681_ = v___x_9675_;
                            v_isShared_9682_ = v_isSharedCheck_9686_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_9679_);
                            leanh::lean_dec(v___x_9675_);
                            v___x_9681_ = leanh::lean_box(0);
                            v_isShared_9682_ = v_isSharedCheck_9686_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_9687_ = lean_array_get_size(v_x_9658_);
                    leanh::lean_inc_ref(v_f_9667_);
                    v___x_9688_ = l_Lean_Meta_getFunInfoNArgs(
                        v_f_9667_,
                        v___x_9687_,
                        v___y_9669_,
                        v___y_9670_,
                        v___y_9671_,
                        v___y_9672_,
                    );
                    if leanh::lean_obj_tag(v___x_9688_) == 0 {
                        v_a_9689_ = leanh::lean_ctor_get(v___x_9688_, 0);
                        leanh::lean_inc(v_a_9689_);
                        leanh::lean_dec_ref_known(v___x_9688_, 1);
                        v_paramInfo_9690_ = leanh::lean_ctor_get(v_a_9689_, 0);
                        leanh::lean_inc_ref(v_paramInfo_9690_);
                        leanh::lean_dec(v_a_9689_);
                        v___x_9691_ = leanh::lean_unsigned_to_nat(0);
                        leanh::lean_inc_ref(v_post_9654_);
                        leanh::lean_inc_ref(v_pre_9653_);
                        v___x_9692_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v___x_9687_, v_paramInfo_9690_, v_pre_9653_, v_post_9654_, v_usedLetOnly_9655_, v_skipConstInApp_9656_, v_skipInstances_9652_, v___x_9691_, v_x_9658_, v___y_9668_, v___y_9669_, v___y_9670_, v___y_9671_, v___y_9672_);
                        leanh::lean_dec_ref(v_paramInfo_9690_);
                        if leanh::lean_obj_tag(v___x_9692_) == 0 {
                            v_a_9693_ = leanh::lean_ctor_get(v___x_9692_, 0);
                            leanh::lean_inc(v_a_9693_);
                            leanh::lean_dec_ref_known(v___x_9692_, 1);
                            v___x_9694_ = l_Lean_mkAppN(v_f_9667_, v_a_9693_);
                            leanh::lean_dec(v_a_9693_);
                            v___x_9695_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_9653_, v_post_9654_, v_usedLetOnly_9655_, v_skipConstInApp_9656_, v_skipInstances_9652_, v___x_9694_, v___y_9668_, v___y_9669_, v___y_9670_, v___y_9671_, v___y_9672_);
                            return v___x_9695_;
                        } else {
                            leanh::lean_dec_ref(v_f_9667_);
                            leanh::lean_dec_ref(v_post_9654_);
                            leanh::lean_dec_ref(v_pre_9653_);
                            v_a_9696_ = leanh::lean_ctor_get(v___x_9692_, 0);
                            v_isSharedCheck_9703_ =
                                (!leanh::lean_is_exclusive(v___x_9692_)) as u8;
                            if v_isSharedCheck_9703_ == 0 {
                                v___x_9698_ = v___x_9692_;
                                v_isShared_9699_ = v_isSharedCheck_9703_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_9696_);
                                leanh::lean_dec(v___x_9692_);
                                v___x_9698_ = leanh::lean_box(0);
                                v_isShared_9699_ = v_isSharedCheck_9703_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_f_9667_);
                        leanh::lean_dec_ref(v_x_9658_);
                        leanh::lean_dec_ref(v_post_9654_);
                        leanh::lean_dec_ref(v_pre_9653_);
                        v_a_9704_ = leanh::lean_ctor_get(v___x_9688_, 0);
                        v_isSharedCheck_9711_ =
                            (!leanh::lean_is_exclusive(v___x_9688_)) as u8;
                        if v_isSharedCheck_9711_ == 0 {
                            v___x_9706_ = v___x_9688_;
                            v_isShared_9707_ = v_isSharedCheck_9711_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_9704_);
                            leanh::lean_dec(v___x_9688_);
                            v___x_9706_ = leanh::lean_box(0);
                            v_isShared_9707_ = v_isSharedCheck_9711_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_9682_ == 0 {
                    v___x_9684_ = v___x_9681_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_9685_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9685_, 0, v_a_9679_);
                    v___x_9684_ = v_reuseFailAlloc_9685_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_9684_;
            }
            4 => {
                if v_isShared_9699_ == 0 {
                    v___x_9701_ = v___x_9698_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_9702_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9702_, 0, v_a_9696_);
                    v___x_9701_ = v_reuseFailAlloc_9702_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_9701_;
            }
            6 => {
                if v_isShared_9707_ == 0 {
                    v___x_9709_ = v___x_9706_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_9710_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9710_, 0, v_a_9704_);
                    v___x_9709_ = v_reuseFailAlloc_9710_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_9709_;
            }
            8 => {
                leanh::lean_inc_ref(v_post_9654_);
                leanh::lean_inc_ref(v_pre_9653_);
                v___x_9713_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_9653_, v_post_9654_, v_usedLetOnly_9655_, v_skipConstInApp_9656_, v_skipInstances_9652_, v_x_9657_, v___y_9660_, v___y_9661_, v___y_9662_, v___y_9663_, v___y_9664_);
                if leanh::lean_obj_tag(v___x_9713_) == 0 {
                    v_a_9714_ = leanh::lean_ctor_get(v___x_9713_, 0);
                    leanh::lean_inc(v_a_9714_);
                    leanh::lean_dec_ref_known(v___x_9713_, 1);
                    v_f_9667_ = v_a_9714_;
                    v___y_9668_ = v___y_9660_;
                    v___y_9669_ = v___y_9661_;
                    v___y_9670_ = v___y_9662_;
                    v___y_9671_ = v___y_9663_;
                    v___y_9672_ = v___y_9664_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_x_9658_);
                    leanh::lean_dec_ref(v_post_9654_);
                    leanh::lean_dec_ref(v_pre_9653_);
                    return v___x_9713_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(
    mut v___x_9722_: *mut leanh::LeanObject,
    mut v_pre_9723_: *mut leanh::LeanObject,
    mut v_e_9724_: *mut leanh::LeanObject,
    mut v_post_9725_: *mut leanh::LeanObject,
    mut v_usedLetOnly_9726_: u8,
    mut v_skipConstInApp_9727_: u8,
    mut v_skipInstances_9728_: u8,
    mut v___y_9729_: *mut leanh::LeanObject,
    mut v___y_9730_: *mut leanh::LeanObject,
    mut v___y_9731_: *mut leanh::LeanObject,
    mut v___y_9732_: *mut leanh::LeanObject,
    mut v___y_9733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9740_: u8 = 0;
    let mut v___y_9742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_9749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_9750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_9755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_9756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9759_: usize = 0;
    let mut v___x_9760_: usize = 0;
    let mut v___x_9761_: u8 = 0;
    let mut v___x_9762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_9765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_9766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_9767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9770_: usize = 0;
    let mut v___x_9771_: usize = 0;
    let mut v___x_9772_: u8 = 0;
    let mut v___x_9773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_9777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_9781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_9783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_9784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9785_: u8 = 0;
    let mut v_a_9786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9789_: u8 = 0;
    let mut v___x_9791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9793_: u8 = 0;
    let mut v_a_9794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9797_: u8 = 0;
    let mut v___x_9799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9801_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9735_ = l_Lean_Core_checkSystem(v___x_9722_, v___y_9732_, v___y_9733_);
                if leanh::lean_obj_tag(v___x_9735_) == 0 {
                    leanh::lean_dec_ref_known(v___x_9735_, 1);
                    leanh::lean_inc_ref(v_pre_9723_);
                    leanh::lean_inc(v___y_9733_);
                    leanh::lean_inc_ref(v___y_9732_);
                    leanh::lean_inc(v___y_9731_);
                    leanh::lean_inc_ref(v___y_9730_);
                    leanh::lean_inc_ref(v_e_9724_);
                    v___x_9736_ = leanh::lean_apply_6(
                        v_pre_9723_,
                        v_e_9724_,
                        v___y_9730_,
                        v___y_9731_,
                        v___y_9732_,
                        v___y_9733_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_9736_) == 0 {
                        v_a_9737_ = leanh::lean_ctor_get(v___x_9736_, 0);
                        v_isSharedCheck_9785_ =
                            (!leanh::lean_is_exclusive(v___x_9736_)) as u8;
                        if v_isSharedCheck_9785_ == 0 {
                            v___x_9739_ = v___x_9736_;
                            v_isShared_9740_ = v_isSharedCheck_9785_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_9737_);
                            leanh::lean_dec(v___x_9736_);
                            v___x_9739_ = leanh::lean_box(0);
                            v_isShared_9740_ = v_isSharedCheck_9785_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_post_9725_);
                        leanh::lean_dec_ref(v_e_9724_);
                        leanh::lean_dec_ref(v_pre_9723_);
                        v_a_9786_ = leanh::lean_ctor_get(v___x_9736_, 0);
                        v_isSharedCheck_9793_ =
                            (!leanh::lean_is_exclusive(v___x_9736_)) as u8;
                        if v_isSharedCheck_9793_ == 0 {
                            v___x_9788_ = v___x_9736_;
                            v_isShared_9789_ = v_isSharedCheck_9793_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_9786_);
                            leanh::lean_dec(v___x_9736_);
                            v___x_9788_ = leanh::lean_box(0);
                            v_isShared_9789_ = v_isSharedCheck_9793_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_post_9725_);
                    leanh::lean_dec_ref(v_e_9724_);
                    leanh::lean_dec_ref(v_pre_9723_);
                    v_a_9794_ = leanh::lean_ctor_get(v___x_9735_, 0);
                    v_isSharedCheck_9801_ = (!leanh::lean_is_exclusive(v___x_9735_)) as u8;
                    if v_isSharedCheck_9801_ == 0 {
                        v___x_9796_ = v___x_9735_;
                        v_isShared_9797_ = v_isSharedCheck_9801_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9794_);
                        leanh::lean_dec(v___x_9735_);
                        v___x_9796_ = leanh::lean_box(0);
                        v_isShared_9797_ = v_isSharedCheck_9801_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => match leanh::lean_obj_tag(v_a_9737_) {
                0 => {
                    leanh::lean_dec_ref(v_post_9725_);
                    leanh::lean_dec_ref(v_e_9724_);
                    leanh::lean_dec_ref(v_pre_9723_);
                    v_e_9777_ = leanh::lean_ctor_get(v_a_9737_, 0);
                    leanh::lean_inc_ref(v_e_9777_);
                    leanh::lean_dec_ref_known(v_a_9737_, 1);
                    if v_isShared_9740_ == 0 {
                        leanh::lean_ctor_set(v___x_9739_, 0, v_e_9777_);
                        v___x_9779_ = v___x_9739_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_9780_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_9780_, 0, v_e_9777_);
                        v___x_9779_ = v_reuseFailAlloc_9780_;
                        state = 3;
                        continue;
                    }
                }
                1 => {
                    leanh::lean_del_object(v___x_9739_);
                    leanh::lean_dec_ref(v_e_9724_);
                    v_e_9781_ = leanh::lean_ctor_get(v_a_9737_, 0);
                    leanh::lean_inc_ref(v_e_9781_);
                    leanh::lean_dec_ref_known(v_a_9737_, 1);
                    v___x_9782_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_9723_, v_post_9725_, v_usedLetOnly_9726_, v_skipConstInApp_9727_, v_skipInstances_9728_, v_e_9781_, v___y_9729_, v___y_9730_, v___y_9731_, v___y_9732_, v___y_9733_);
                    return v___x_9782_;
                }
                _ => {
                    leanh::lean_del_object(v___x_9739_);
                    v_e_x3f_9783_ = leanh::lean_ctor_get(v_a_9737_, 0);
                    leanh::lean_inc(v_e_x3f_9783_);
                    leanh::lean_dec_ref_known(v_a_9737_, 1);
                    if leanh::lean_obj_tag(v_e_x3f_9783_) == 0 {
                        v___y_9742_ = v_e_9724_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_e_9724_);
                        v_val_9784_ = leanh::lean_ctor_get(v_e_x3f_9783_, 0);
                        leanh::lean_inc(v_val_9784_);
                        leanh::lean_dec_ref_known(v_e_x3f_9783_, 1);
                        v___y_9742_ = v_val_9784_;
                        state = 2;
                        continue;
                    }
                }
            },
            2 => match leanh::lean_obj_tag(v___y_9742_) {
                7 => {
                    v___x_9743_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0;
                    v___x_9744_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_9723_, v_post_9725_, v_usedLetOnly_9726_, v_skipConstInApp_9727_, v_skipInstances_9728_, v___x_9743_, v___y_9742_, v___y_9729_, v___y_9730_, v___y_9731_, v___y_9732_, v___y_9733_);
                    return v___x_9744_;
                }
                6 => {
                    v___x_9745_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0;
                    v___x_9746_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_9723_, v_post_9725_, v_usedLetOnly_9726_, v_skipConstInApp_9727_, v_skipInstances_9728_, v___x_9745_, v___y_9742_, v___y_9729_, v___y_9730_, v___y_9731_, v___y_9732_, v___y_9733_);
                    return v___x_9746_;
                }
                8 => {
                    v___x_9747_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0;
                    v___x_9748_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_9723_, v_post_9725_, v_usedLetOnly_9726_, v_skipConstInApp_9727_, v_skipInstances_9728_, v___x_9747_, v___y_9742_, v___y_9729_, v___y_9730_, v___y_9731_, v___y_9732_, v___y_9733_);
                    return v___x_9748_;
                }
                5 => {
                    v_dummy_9749_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once), _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
                    v_nargs_9750_ = l_Lean_Expr_getAppNumArgs(v___y_9742_);
                    leanh::lean_inc(v_nargs_9750_);
                    v___x_9751_ = lean_mk_array(v_nargs_9750_, v_dummy_9749_);
                    v___x_9752_ = leanh::lean_unsigned_to_nat(1);
                    v___x_9753_ = lean_nat_sub(v_nargs_9750_, v___x_9752_);
                    leanh::lean_dec(v_nargs_9750_);
                    v___x_9754_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_9728_, v_pre_9723_, v_post_9725_, v_usedLetOnly_9726_, v_skipConstInApp_9727_, v___y_9742_, v___x_9751_, v___x_9753_, v___y_9729_, v___y_9730_, v___y_9731_, v___y_9732_, v___y_9733_);
                    return v___x_9754_;
                }
                10 => {
                    v_data_9755_ = leanh::lean_ctor_get(v___y_9742_, 0);
                    v_expr_9756_ = leanh::lean_ctor_get(v___y_9742_, 1);
                    leanh::lean_inc_ref(v_expr_9756_);
                    leanh::lean_inc_ref(v_post_9725_);
                    leanh::lean_inc_ref(v_pre_9723_);
                    v___x_9757_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_9723_, v_post_9725_, v_usedLetOnly_9726_, v_skipConstInApp_9727_, v_skipInstances_9728_, v_expr_9756_, v___y_9729_, v___y_9730_, v___y_9731_, v___y_9732_, v___y_9733_);
                    if leanh::lean_obj_tag(v___x_9757_) == 0 {
                        v_a_9758_ = leanh::lean_ctor_get(v___x_9757_, 0);
                        leanh::lean_inc(v_a_9758_);
                        leanh::lean_dec_ref_known(v___x_9757_, 1);
                        v___x_9759_ = lean_ptr_addr(v_expr_9756_);
                        v___x_9760_ = lean_ptr_addr(v_a_9758_);
                        v___x_9761_ = lean_usize_dec_eq(v___x_9759_, v___x_9760_);
                        if v___x_9761_ == 0 {
                            leanh::lean_inc(v_data_9755_);
                            leanh::lean_dec_ref_known(v___y_9742_, 2);
                            v___x_9762_ = l_Lean_Expr_mdata___override(v_data_9755_, v_a_9758_);
                            v___x_9763_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_9723_, v_post_9725_, v_usedLetOnly_9726_, v_skipConstInApp_9727_, v_skipInstances_9728_, v___x_9762_, v___y_9729_, v___y_9730_, v___y_9731_, v___y_9732_, v___y_9733_);
                            return v___x_9763_;
                        } else {
                            leanh::lean_dec(v_a_9758_);
                            v___x_9764_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_9723_, v_post_9725_, v_usedLetOnly_9726_, v_skipConstInApp_9727_, v_skipInstances_9728_, v___y_9742_, v___y_9729_, v___y_9730_, v___y_9731_, v___y_9732_, v___y_9733_);
                            return v___x_9764_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___y_9742_, 2);
                        leanh::lean_dec_ref(v_post_9725_);
                        leanh::lean_dec_ref(v_pre_9723_);
                        return v___x_9757_;
                    }
                }
                11 => {
                    v_typeName_9765_ = leanh::lean_ctor_get(v___y_9742_, 0);
                    v_idx_9766_ = leanh::lean_ctor_get(v___y_9742_, 1);
                    v_struct_9767_ = leanh::lean_ctor_get(v___y_9742_, 2);
                    leanh::lean_inc_ref(v_struct_9767_);
                    leanh::lean_inc_ref(v_post_9725_);
                    leanh::lean_inc_ref(v_pre_9723_);
                    v___x_9768_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_9723_, v_post_9725_, v_usedLetOnly_9726_, v_skipConstInApp_9727_, v_skipInstances_9728_, v_struct_9767_, v___y_9729_, v___y_9730_, v___y_9731_, v___y_9732_, v___y_9733_);
                    if leanh::lean_obj_tag(v___x_9768_) == 0 {
                        v_a_9769_ = leanh::lean_ctor_get(v___x_9768_, 0);
                        leanh::lean_inc(v_a_9769_);
                        leanh::lean_dec_ref_known(v___x_9768_, 1);
                        v___x_9770_ = lean_ptr_addr(v_struct_9767_);
                        v___x_9771_ = lean_ptr_addr(v_a_9769_);
                        v___x_9772_ = lean_usize_dec_eq(v___x_9770_, v___x_9771_);
                        if v___x_9772_ == 0 {
                            leanh::lean_inc(v_idx_9766_);
                            leanh::lean_inc(v_typeName_9765_);
                            leanh::lean_dec_ref_known(v___y_9742_, 3);
                            v___x_9773_ = l_Lean_Expr_proj___override(
                                v_typeName_9765_,
                                v_idx_9766_,
                                v_a_9769_,
                            );
                            v___x_9774_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_9723_, v_post_9725_, v_usedLetOnly_9726_, v_skipConstInApp_9727_, v_skipInstances_9728_, v___x_9773_, v___y_9729_, v___y_9730_, v___y_9731_, v___y_9732_, v___y_9733_);
                            return v___x_9774_;
                        } else {
                            leanh::lean_dec(v_a_9769_);
                            v___x_9775_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_9723_, v_post_9725_, v_usedLetOnly_9726_, v_skipConstInApp_9727_, v_skipInstances_9728_, v___y_9742_, v___y_9729_, v___y_9730_, v___y_9731_, v___y_9732_, v___y_9733_);
                            return v___x_9775_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___y_9742_, 3);
                        leanh::lean_dec_ref(v_post_9725_);
                        leanh::lean_dec_ref(v_pre_9723_);
                        return v___x_9768_;
                    }
                }
                _ => {
                    v___x_9776_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_9723_, v_post_9725_, v_usedLetOnly_9726_, v_skipConstInApp_9727_, v_skipInstances_9728_, v___y_9742_, v___y_9729_, v___y_9730_, v___y_9731_, v___y_9732_, v___y_9733_);
                    return v___x_9776_;
                }
            },
            3 => {
                return v___x_9779_;
            }
            4 => {
                if v_isShared_9789_ == 0 {
                    v___x_9791_ = v___x_9788_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_9792_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9792_, 0, v_a_9786_);
                    v___x_9791_ = v_reuseFailAlloc_9792_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_9791_;
            }
            6 => {
                if v_isShared_9797_ == 0 {
                    v___x_9799_ = v___x_9796_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_9800_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9800_, 0, v_a_9794_);
                    v___x_9799_ = v_reuseFailAlloc_9800_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_9799_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed(
    mut v___x_9802_: *mut leanh::LeanObject,
    mut v_pre_9803_: *mut leanh::LeanObject,
    mut v_e_9804_: *mut leanh::LeanObject,
    mut v_post_9805_: *mut leanh::LeanObject,
    mut v_usedLetOnly_9806_: *mut leanh::LeanObject,
    mut v_skipConstInApp_9807_: *mut leanh::LeanObject,
    mut v_skipInstances_9808_: *mut leanh::LeanObject,
    mut v___y_9809_: *mut leanh::LeanObject,
    mut v___y_9810_: *mut leanh::LeanObject,
    mut v___y_9811_: *mut leanh::LeanObject,
    mut v___y_9812_: *mut leanh::LeanObject,
    mut v___y_9813_: *mut leanh::LeanObject,
    mut v___y_9814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_9815_: u8 = 0;
    let mut v_skipConstInApp_boxed_9816_: u8 = 0;
    let mut v_skipInstances_boxed_9817_: u8 = 0;
    let mut v_res_9818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_9815_ = (leanh::lean_unbox(v_usedLetOnly_9806_) as u8);
    v_skipConstInApp_boxed_9816_ = (leanh::lean_unbox(v_skipConstInApp_9807_) as u8);
    v_skipInstances_boxed_9817_ = (leanh::lean_unbox(v_skipInstances_9808_) as u8);
    v_res_9818_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(v___x_9802_, v_pre_9803_, v_e_9804_, v_post_9805_, v_usedLetOnly_boxed_9815_, v_skipConstInApp_boxed_9816_, v_skipInstances_boxed_9817_, v___y_9809_, v___y_9810_, v___y_9811_, v___y_9812_, v___y_9813_);
    leanh::lean_dec(v___y_9813_);
    leanh::lean_dec_ref(v___y_9812_);
    leanh::lean_dec(v___y_9811_);
    leanh::lean_dec_ref(v___y_9810_);
    leanh::lean_dec(v___y_9809_);
    return v_res_9818_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(
    mut v_pre_9819_: *mut leanh::LeanObject,
    mut v_post_9820_: *mut leanh::LeanObject,
    mut v_usedLetOnly_9821_: u8,
    mut v_skipConstInApp_9822_: u8,
    mut v_skipInstances_9823_: u8,
    mut v_e_9824_: *mut leanh::LeanObject,
    mut v_a_9825_: *mut leanh::LeanObject,
    mut v___y_9826_: *mut leanh::LeanObject,
    mut v___y_9827_: *mut leanh::LeanObject,
    mut v___y_9828_: *mut leanh::LeanObject,
    mut v___y_9829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9836_: u8 = 0;
    let mut v___x_9837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_9842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_9845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9849_: u8 = 0;
    let mut v___x_9851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9853_: u8 = 0;
    let mut v_unused_9854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9858_: u8 = 0;
    let mut v___x_9860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9862_: u8 = 0;
    let mut v_val_9863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9867_: u8 = 0;
    let mut v_a_9868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9871_: u8 = 0;
    let mut v___x_9873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9875_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_9825_);
                v___x_9831_ = leanh::lean_alloc_closure(
                    l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___x_9831_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_9831_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_9831_, 2, v_a_9825_);
                v___x_9832_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(leanh::lean_box(0), v___x_9831_, v___y_9826_, v___y_9827_, v___y_9828_, v___y_9829_);
                if leanh::lean_obj_tag(v___x_9832_) == 0 {
                    v_a_9833_ = leanh::lean_ctor_get(v___x_9832_, 0);
                    v_isSharedCheck_9867_ = (!leanh::lean_is_exclusive(v___x_9832_)) as u8;
                    if v_isSharedCheck_9867_ == 0 {
                        v___x_9835_ = v___x_9832_;
                        v_isShared_9836_ = v_isSharedCheck_9867_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9833_);
                        leanh::lean_dec(v___x_9832_);
                        v___x_9835_ = leanh::lean_box(0);
                        v_isShared_9836_ = v_isSharedCheck_9867_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_9824_);
                    leanh::lean_dec_ref(v_post_9820_);
                    leanh::lean_dec_ref(v_pre_9819_);
                    v_a_9868_ = leanh::lean_ctor_get(v___x_9832_, 0);
                    v_isSharedCheck_9875_ = (!leanh::lean_is_exclusive(v___x_9832_)) as u8;
                    if v_isSharedCheck_9875_ == 0 {
                        v___x_9870_ = v___x_9832_;
                        v_isShared_9871_ = v_isSharedCheck_9875_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9868_);
                        leanh::lean_dec(v___x_9832_);
                        v___x_9870_ = leanh::lean_box(0);
                        v_isShared_9871_ = v_isSharedCheck_9875_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_9837_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_a_9833_, v_e_9824_);
                leanh::lean_dec(v_a_9833_);
                if leanh::lean_obj_tag(v___x_9837_) == 0 {
                    leanh::lean_del_object(v___x_9835_);
                    v___x_9838_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0;
                    v___x_9839_ = leanh::lean_box((v_usedLetOnly_9821_) as usize);
                    v___x_9840_ = leanh::lean_box((v_skipConstInApp_9822_) as usize);
                    v___x_9841_ = leanh::lean_box((v_skipInstances_9823_) as usize);
                    leanh::lean_inc_ref(v_e_9824_);
                    v___f_9842_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed as *mut core::ffi::c_void, 13, 7);
                    leanh::lean_closure_set(v___f_9842_, 0, v___x_9838_);
                    leanh::lean_closure_set(v___f_9842_, 1, v_pre_9819_);
                    leanh::lean_closure_set(v___f_9842_, 2, v_e_9824_);
                    leanh::lean_closure_set(v___f_9842_, 3, v_post_9820_);
                    leanh::lean_closure_set(v___f_9842_, 4, v___x_9839_);
                    leanh::lean_closure_set(v___f_9842_, 5, v___x_9840_);
                    leanh::lean_closure_set(v___f_9842_, 6, v___x_9841_);
                    v___x_9843_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v___f_9842_, v_a_9825_, v___y_9826_, v___y_9827_, v___y_9828_, v___y_9829_);
                    if leanh::lean_obj_tag(v___x_9843_) == 0 {
                        v_a_9844_ = leanh::lean_ctor_get(v___x_9843_, 0);
                        leanh::lean_inc_n(v_a_9844_, 2);
                        leanh::lean_dec_ref_known(v___x_9843_, 1);
                        leanh::lean_inc(v_a_9825_);
                        v___f_9845_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed as *mut core::ffi::c_void, 4, 3);
                        leanh::lean_closure_set(v___f_9845_, 0, v_a_9825_);
                        leanh::lean_closure_set(v___f_9845_, 1, v_e_9824_);
                        leanh::lean_closure_set(v___f_9845_, 2, v_a_9844_);
                        v___x_9846_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(leanh::lean_box(0), v___f_9845_, v___y_9826_, v___y_9827_, v___y_9828_, v___y_9829_);
                        if leanh::lean_obj_tag(v___x_9846_) == 0 {
                            v_isSharedCheck_9853_ =
                                (!leanh::lean_is_exclusive(v___x_9846_)) as u8;
                            if v_isSharedCheck_9853_ == 0 {
                                v_unused_9854_ = leanh::lean_ctor_get(v___x_9846_, 0);
                                leanh::lean_dec(v_unused_9854_);
                                v___x_9848_ = v___x_9846_;
                                v_isShared_9849_ = v_isSharedCheck_9853_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_9846_);
                                v___x_9848_ = leanh::lean_box(0);
                                v_isShared_9849_ = v_isSharedCheck_9853_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_9844_);
                            v_a_9855_ = leanh::lean_ctor_get(v___x_9846_, 0);
                            v_isSharedCheck_9862_ =
                                (!leanh::lean_is_exclusive(v___x_9846_)) as u8;
                            if v_isSharedCheck_9862_ == 0 {
                                v___x_9857_ = v___x_9846_;
                                v_isShared_9858_ = v_isSharedCheck_9862_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_9855_);
                                leanh::lean_dec(v___x_9846_);
                                v___x_9857_ = leanh::lean_box(0);
                                v_isShared_9858_ = v_isSharedCheck_9862_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_9824_);
                        return v___x_9843_;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_9824_);
                    leanh::lean_dec_ref(v_post_9820_);
                    leanh::lean_dec_ref(v_pre_9819_);
                    v_val_9863_ = leanh::lean_ctor_get(v___x_9837_, 0);
                    leanh::lean_inc(v_val_9863_);
                    leanh::lean_dec_ref_known(v___x_9837_, 1);
                    if v_isShared_9836_ == 0 {
                        leanh::lean_ctor_set(v___x_9835_, 0, v_val_9863_);
                        v___x_9865_ = v___x_9835_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_9866_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_9866_, 0, v_val_9863_);
                        v___x_9865_ = v_reuseFailAlloc_9866_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_9849_ == 0 {
                    leanh::lean_ctor_set(v___x_9848_, 0, v_a_9844_);
                    v___x_9851_ = v___x_9848_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_9852_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9852_, 0, v_a_9844_);
                    v___x_9851_ = v_reuseFailAlloc_9852_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_9851_;
            }
            4 => {
                if v_isShared_9858_ == 0 {
                    v___x_9860_ = v___x_9857_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_9861_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9861_, 0, v_a_9855_);
                    v___x_9860_ = v_reuseFailAlloc_9861_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_9860_;
            }
            6 => {
                return v___x_9865_;
            }
            7 => {
                if v_isShared_9871_ == 0 {
                    v___x_9873_ = v___x_9870_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_9874_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9874_, 0, v_a_9868_);
                    v___x_9873_ = v_reuseFailAlloc_9874_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_9873_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed(
    mut v_fvars_9876_: *mut leanh::LeanObject,
    mut v_pre_9877_: *mut leanh::LeanObject,
    mut v_post_9878_: *mut leanh::LeanObject,
    mut v_usedLetOnly_9879_: *mut leanh::LeanObject,
    mut v_skipConstInApp_9880_: *mut leanh::LeanObject,
    mut v_skipInstances_9881_: *mut leanh::LeanObject,
    mut v_body_9882_: *mut leanh::LeanObject,
    mut v_x_9883_: *mut leanh::LeanObject,
    mut v___y_9884_: *mut leanh::LeanObject,
    mut v___y_9885_: *mut leanh::LeanObject,
    mut v___y_9886_: *mut leanh::LeanObject,
    mut v___y_9887_: *mut leanh::LeanObject,
    mut v___y_9888_: *mut leanh::LeanObject,
    mut v___y_9889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_9890_: u8 = 0;
    let mut v_skipConstInApp_boxed_9891_: u8 = 0;
    let mut v_skipInstances_boxed_9892_: u8 = 0;
    let mut v_res_9893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_9890_ = (leanh::lean_unbox(v_usedLetOnly_9879_) as u8);
    v_skipConstInApp_boxed_9891_ = (leanh::lean_unbox(v_skipConstInApp_9880_) as u8);
    v_skipInstances_boxed_9892_ = (leanh::lean_unbox(v_skipInstances_9881_) as u8);
    v_res_9893_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(v_fvars_9876_, v_pre_9877_, v_post_9878_, v_usedLetOnly_boxed_9890_, v_skipConstInApp_boxed_9891_, v_skipInstances_boxed_9892_, v_body_9882_, v_x_9883_, v___y_9884_, v___y_9885_, v___y_9886_, v___y_9887_, v___y_9888_);
    leanh::lean_dec(v___y_9888_);
    leanh::lean_dec_ref(v___y_9887_);
    leanh::lean_dec(v___y_9886_);
    leanh::lean_dec_ref(v___y_9885_);
    leanh::lean_dec(v___y_9884_);
    return v_res_9893_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(
    mut v_pre_9894_: *mut leanh::LeanObject,
    mut v_post_9895_: *mut leanh::LeanObject,
    mut v_usedLetOnly_9896_: u8,
    mut v_skipConstInApp_9897_: u8,
    mut v_skipInstances_9898_: u8,
    mut v_fvars_9899_: *mut leanh::LeanObject,
    mut v_e_9900_: *mut leanh::LeanObject,
    mut v_a_9901_: *mut leanh::LeanObject,
    mut v___y_9902_: *mut leanh::LeanObject,
    mut v___y_9903_: *mut leanh::LeanObject,
    mut v___y_9904_: *mut leanh::LeanObject,
    mut v___y_9905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_e_9900_) == 7 {
        let mut v_binderName_9907_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_9908_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_9909_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_9910_: u8 = 0;
        let mut v___x_9911_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_9912_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_binderName_9907_ = leanh::lean_ctor_get(v_e_9900_, 0);
        leanh::lean_inc(v_binderName_9907_);
        v_binderType_9908_ = leanh::lean_ctor_get(v_e_9900_, 1);
        leanh::lean_inc_ref(v_binderType_9908_);
        v_body_9909_ = leanh::lean_ctor_get(v_e_9900_, 2);
        leanh::lean_inc_ref(v_body_9909_);
        v_binderInfo_9910_ = leanh::lean_ctor_get_uint8(
            v_e_9900_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
        );
        leanh::lean_dec_ref_known(v_e_9900_, 3);
        v___x_9911_ = lean_expr_instantiate_rev(v_binderType_9908_, v_fvars_9899_);
        leanh::lean_dec_ref(v_binderType_9908_);
        leanh::lean_inc_ref(v_post_9895_);
        leanh::lean_inc_ref(v_pre_9894_);
        v___x_9912_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_9894_, v_post_9895_, v_usedLetOnly_9896_, v_skipConstInApp_9897_, v_skipInstances_9898_, v___x_9911_, v_a_9901_, v___y_9902_, v___y_9903_, v___y_9904_, v___y_9905_);
        if leanh::lean_obj_tag(v___x_9912_) == 0 {
            let mut v_a_9913_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_9914_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_9915_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_9916_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_9917_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_9918_: u8 = 0;
            let mut v___x_9919_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_9913_ = leanh::lean_ctor_get(v___x_9912_, 0);
            leanh::lean_inc(v_a_9913_);
            leanh::lean_dec_ref_known(v___x_9912_, 1);
            v___x_9914_ = leanh::lean_box((v_usedLetOnly_9896_) as usize);
            v___x_9915_ = leanh::lean_box((v_skipConstInApp_9897_) as usize);
            v___x_9916_ = leanh::lean_box((v_skipInstances_9898_) as usize);
            v___f_9917_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed as *mut core::ffi::c_void, 14, 7);
            leanh::lean_closure_set(v___f_9917_, 0, v_fvars_9899_);
            leanh::lean_closure_set(v___f_9917_, 1, v_pre_9894_);
            leanh::lean_closure_set(v___f_9917_, 2, v_post_9895_);
            leanh::lean_closure_set(v___f_9917_, 3, v___x_9914_);
            leanh::lean_closure_set(v___f_9917_, 4, v___x_9915_);
            leanh::lean_closure_set(v___f_9917_, 5, v___x_9916_);
            leanh::lean_closure_set(v___f_9917_, 6, v_body_9909_);
            v___x_9918_ = 0;
            v___x_9919_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_9907_, v_binderInfo_9910_, v_a_9913_, v___f_9917_, v___x_9918_, v_a_9901_, v___y_9902_, v___y_9903_, v___y_9904_, v___y_9905_);
            return v___x_9919_;
        } else {
            leanh::lean_dec_ref(v_body_9909_);
            leanh::lean_dec(v_binderName_9907_);
            leanh::lean_dec_ref(v_fvars_9899_);
            leanh::lean_dec_ref(v_post_9895_);
            leanh::lean_dec_ref(v_pre_9894_);
            return v___x_9912_;
        }
    } else {
        let mut v___x_9920_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_9921_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_9920_ = lean_expr_instantiate_rev(v_e_9900_, v_fvars_9899_);
        leanh::lean_dec_ref(v_e_9900_);
        leanh::lean_inc_ref(v_post_9895_);
        leanh::lean_inc_ref(v_pre_9894_);
        v___x_9921_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_9894_, v_post_9895_, v_usedLetOnly_9896_, v_skipConstInApp_9897_, v_skipInstances_9898_, v___x_9920_, v_a_9901_, v___y_9902_, v___y_9903_, v___y_9904_, v___y_9905_);
        if leanh::lean_obj_tag(v___x_9921_) == 0 {
            let mut v_a_9922_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_9923_: u8 = 0;
            let mut v___x_9924_: u8 = 0;
            let mut v___x_9925_: u8 = 0;
            let mut v___x_9926_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_9922_ = leanh::lean_ctor_get(v___x_9921_, 0);
            leanh::lean_inc(v_a_9922_);
            leanh::lean_dec_ref_known(v___x_9921_, 1);
            v___x_9923_ = 0;
            v___x_9924_ = 1;
            v___x_9925_ = 1;
            v___x_9926_ = l_Lean_Meta_mkForallFVars(
                v_fvars_9899_,
                v_a_9922_,
                v___x_9923_,
                v_usedLetOnly_9896_,
                v___x_9924_,
                v___x_9925_,
                v___y_9902_,
                v___y_9903_,
                v___y_9904_,
                v___y_9905_,
            );
            leanh::lean_dec_ref(v_fvars_9899_);
            if leanh::lean_obj_tag(v___x_9926_) == 0 {
                let mut v_a_9927_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_9928_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_a_9927_ = leanh::lean_ctor_get(v___x_9926_, 0);
                leanh::lean_inc(v_a_9927_);
                leanh::lean_dec_ref_known(v___x_9926_, 1);
                v___x_9928_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_9894_, v_post_9895_, v_usedLetOnly_9896_, v_skipConstInApp_9897_, v_skipInstances_9898_, v_a_9927_, v_a_9901_, v___y_9902_, v___y_9903_, v___y_9904_, v___y_9905_);
                return v___x_9928_;
            } else {
                leanh::lean_dec_ref(v_post_9895_);
                leanh::lean_dec_ref(v_pre_9894_);
                return v___x_9926_;
            }
        } else {
            leanh::lean_dec_ref(v_fvars_9899_);
            leanh::lean_dec_ref(v_post_9895_);
            leanh::lean_dec_ref(v_pre_9894_);
            return v___x_9921_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(
    mut v_fvars_9929_: *mut leanh::LeanObject,
    mut v_pre_9930_: *mut leanh::LeanObject,
    mut v_post_9931_: *mut leanh::LeanObject,
    mut v_usedLetOnly_9932_: u8,
    mut v_skipConstInApp_9933_: u8,
    mut v_skipInstances_9934_: u8,
    mut v_body_9935_: *mut leanh::LeanObject,
    mut v_x_9936_: *mut leanh::LeanObject,
    mut v___y_9937_: *mut leanh::LeanObject,
    mut v___y_9938_: *mut leanh::LeanObject,
    mut v___y_9939_: *mut leanh::LeanObject,
    mut v___y_9940_: *mut leanh::LeanObject,
    mut v___y_9941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9943_ = lean_array_push(v_fvars_9929_, v_x_9936_);
    v___x_9944_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_9930_, v_post_9931_, v_usedLetOnly_9932_, v_skipConstInApp_9933_, v_skipInstances_9934_, v___x_9943_, v_body_9935_, v___y_9937_, v___y_9938_, v___y_9939_, v___y_9940_, v___y_9941_);
    return v___x_9944_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3___boxed(
    mut v_pre_9945_: *mut leanh::LeanObject,
    mut v_post_9946_: *mut leanh::LeanObject,
    mut v_usedLetOnly_9947_: *mut leanh::LeanObject,
    mut v_skipConstInApp_9948_: *mut leanh::LeanObject,
    mut v_skipInstances_9949_: *mut leanh::LeanObject,
    mut v_e_9950_: *mut leanh::LeanObject,
    mut v_a_9951_: *mut leanh::LeanObject,
    mut v___y_9952_: *mut leanh::LeanObject,
    mut v___y_9953_: *mut leanh::LeanObject,
    mut v___y_9954_: *mut leanh::LeanObject,
    mut v___y_9955_: *mut leanh::LeanObject,
    mut v___y_9956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_9957_: u8 = 0;
    let mut v_skipConstInApp_boxed_9958_: u8 = 0;
    let mut v_skipInstances_boxed_9959_: u8 = 0;
    let mut v_res_9960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_9957_ = (leanh::lean_unbox(v_usedLetOnly_9947_) as u8);
    v_skipConstInApp_boxed_9958_ = (leanh::lean_unbox(v_skipConstInApp_9948_) as u8);
    v_skipInstances_boxed_9959_ = (leanh::lean_unbox(v_skipInstances_9949_) as u8);
    v_res_9960_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_9945_, v_post_9946_, v_usedLetOnly_boxed_9957_, v_skipConstInApp_boxed_9958_, v_skipInstances_boxed_9959_, v_e_9950_, v_a_9951_, v___y_9952_, v___y_9953_, v___y_9954_, v___y_9955_);
    leanh::lean_dec(v___y_9955_);
    leanh::lean_dec_ref(v___y_9954_);
    leanh::lean_dec(v___y_9953_);
    leanh::lean_dec_ref(v___y_9952_);
    leanh::lean_dec(v_a_9951_);
    return v_res_9960_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2___boxed(
    mut v_pre_9961_: *mut leanh::LeanObject,
    mut v_post_9962_: *mut leanh::LeanObject,
    mut v_usedLetOnly_9963_: *mut leanh::LeanObject,
    mut v_skipConstInApp_9964_: *mut leanh::LeanObject,
    mut v_skipInstances_9965_: *mut leanh::LeanObject,
    mut v_sz_9966_: *mut leanh::LeanObject,
    mut v_i_9967_: *mut leanh::LeanObject,
    mut v_bs_9968_: *mut leanh::LeanObject,
    mut v___y_9969_: *mut leanh::LeanObject,
    mut v___y_9970_: *mut leanh::LeanObject,
    mut v___y_9971_: *mut leanh::LeanObject,
    mut v___y_9972_: *mut leanh::LeanObject,
    mut v___y_9973_: *mut leanh::LeanObject,
    mut v___y_9974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_9975_: u8 = 0;
    let mut v_skipConstInApp_boxed_9976_: u8 = 0;
    let mut v_skipInstances_boxed_9977_: u8 = 0;
    let mut v_sz_boxed_9978_: usize = 0;
    let mut v_i_boxed_9979_: usize = 0;
    let mut v_res_9980_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_9975_ = (leanh::lean_unbox(v_usedLetOnly_9963_) as u8);
    v_skipConstInApp_boxed_9976_ = (leanh::lean_unbox(v_skipConstInApp_9964_) as u8);
    v_skipInstances_boxed_9977_ = (leanh::lean_unbox(v_skipInstances_9965_) as u8);
    v_sz_boxed_9978_ = leanh::lean_unbox_usize(v_sz_9966_);
    leanh::lean_dec(v_sz_9966_);
    v_i_boxed_9979_ = leanh::lean_unbox_usize(v_i_9967_);
    leanh::lean_dec(v_i_9967_);
    v_res_9980_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_9961_, v_post_9962_, v_usedLetOnly_boxed_9975_, v_skipConstInApp_boxed_9976_, v_skipInstances_boxed_9977_, v_sz_boxed_9978_, v_i_boxed_9979_, v_bs_9968_, v___y_9969_, v___y_9970_, v___y_9971_, v___y_9972_, v___y_9973_);
    leanh::lean_dec(v___y_9973_);
    leanh::lean_dec_ref(v___y_9972_);
    leanh::lean_dec(v___y_9971_);
    leanh::lean_dec_ref(v___y_9970_);
    leanh::lean_dec(v___y_9969_);
    return v_res_9980_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___boxed(
    mut v_pre_9981_: *mut leanh::LeanObject,
    mut v_post_9982_: *mut leanh::LeanObject,
    mut v_usedLetOnly_9983_: *mut leanh::LeanObject,
    mut v_skipConstInApp_9984_: *mut leanh::LeanObject,
    mut v_skipInstances_9985_: *mut leanh::LeanObject,
    mut v_e_9986_: *mut leanh::LeanObject,
    mut v_a_9987_: *mut leanh::LeanObject,
    mut v___y_9988_: *mut leanh::LeanObject,
    mut v___y_9989_: *mut leanh::LeanObject,
    mut v___y_9990_: *mut leanh::LeanObject,
    mut v___y_9991_: *mut leanh::LeanObject,
    mut v___y_9992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_9993_: u8 = 0;
    let mut v_skipConstInApp_boxed_9994_: u8 = 0;
    let mut v_skipInstances_boxed_9995_: u8 = 0;
    let mut v_res_9996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_9993_ = (leanh::lean_unbox(v_usedLetOnly_9983_) as u8);
    v_skipConstInApp_boxed_9994_ = (leanh::lean_unbox(v_skipConstInApp_9984_) as u8);
    v_skipInstances_boxed_9995_ = (leanh::lean_unbox(v_skipInstances_9985_) as u8);
    v_res_9996_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_9981_, v_post_9982_, v_usedLetOnly_boxed_9993_, v_skipConstInApp_boxed_9994_, v_skipInstances_boxed_9995_, v_e_9986_, v_a_9987_, v___y_9988_, v___y_9989_, v___y_9990_, v___y_9991_);
    leanh::lean_dec(v___y_9991_);
    leanh::lean_dec_ref(v___y_9990_);
    leanh::lean_dec(v___y_9989_);
    leanh::lean_dec_ref(v___y_9988_);
    leanh::lean_dec(v_a_9987_);
    return v_res_9996_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___boxed(
    mut v_pre_9997_: *mut leanh::LeanObject,
    mut v_post_9998_: *mut leanh::LeanObject,
    mut v_usedLetOnly_9999_: *mut leanh::LeanObject,
    mut v_skipConstInApp_10000_: *mut leanh::LeanObject,
    mut v_skipInstances_10001_: *mut leanh::LeanObject,
    mut v_fvars_10002_: *mut leanh::LeanObject,
    mut v_e_10003_: *mut leanh::LeanObject,
    mut v_a_10004_: *mut leanh::LeanObject,
    mut v___y_10005_: *mut leanh::LeanObject,
    mut v___y_10006_: *mut leanh::LeanObject,
    mut v___y_10007_: *mut leanh::LeanObject,
    mut v___y_10008_: *mut leanh::LeanObject,
    mut v___y_10009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_10010_: u8 = 0;
    let mut v_skipConstInApp_boxed_10011_: u8 = 0;
    let mut v_skipInstances_boxed_10012_: u8 = 0;
    let mut v_res_10013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_10010_ = (leanh::lean_unbox(v_usedLetOnly_9999_) as u8);
    v_skipConstInApp_boxed_10011_ = (leanh::lean_unbox(v_skipConstInApp_10000_) as u8);
    v_skipInstances_boxed_10012_ = (leanh::lean_unbox(v_skipInstances_10001_) as u8);
    v_res_10013_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_9997_, v_post_9998_, v_usedLetOnly_boxed_10010_, v_skipConstInApp_boxed_10011_, v_skipInstances_boxed_10012_, v_fvars_10002_, v_e_10003_, v_a_10004_, v___y_10005_, v___y_10006_, v___y_10007_, v___y_10008_);
    leanh::lean_dec(v___y_10008_);
    leanh::lean_dec_ref(v___y_10007_);
    leanh::lean_dec(v___y_10006_);
    leanh::lean_dec_ref(v___y_10005_);
    leanh::lean_dec(v_a_10004_);
    return v_res_10013_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___boxed(
    mut v_pre_10014_: *mut leanh::LeanObject,
    mut v_post_10015_: *mut leanh::LeanObject,
    mut v_usedLetOnly_10016_: *mut leanh::LeanObject,
    mut v_skipConstInApp_10017_: *mut leanh::LeanObject,
    mut v_skipInstances_10018_: *mut leanh::LeanObject,
    mut v_fvars_10019_: *mut leanh::LeanObject,
    mut v_e_10020_: *mut leanh::LeanObject,
    mut v_a_10021_: *mut leanh::LeanObject,
    mut v___y_10022_: *mut leanh::LeanObject,
    mut v___y_10023_: *mut leanh::LeanObject,
    mut v___y_10024_: *mut leanh::LeanObject,
    mut v___y_10025_: *mut leanh::LeanObject,
    mut v___y_10026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_10027_: u8 = 0;
    let mut v_skipConstInApp_boxed_10028_: u8 = 0;
    let mut v_skipInstances_boxed_10029_: u8 = 0;
    let mut v_res_10030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_10027_ = (leanh::lean_unbox(v_usedLetOnly_10016_) as u8);
    v_skipConstInApp_boxed_10028_ = (leanh::lean_unbox(v_skipConstInApp_10017_) as u8);
    v_skipInstances_boxed_10029_ = (leanh::lean_unbox(v_skipInstances_10018_) as u8);
    v_res_10030_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_10014_, v_post_10015_, v_usedLetOnly_boxed_10027_, v_skipConstInApp_boxed_10028_, v_skipInstances_boxed_10029_, v_fvars_10019_, v_e_10020_, v_a_10021_, v___y_10022_, v___y_10023_, v___y_10024_, v___y_10025_);
    leanh::lean_dec(v___y_10025_);
    leanh::lean_dec_ref(v___y_10024_);
    leanh::lean_dec(v___y_10023_);
    leanh::lean_dec_ref(v___y_10022_);
    leanh::lean_dec(v_a_10021_);
    return v_res_10030_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___boxed(
    mut v_pre_10031_: *mut leanh::LeanObject,
    mut v_post_10032_: *mut leanh::LeanObject,
    mut v_usedLetOnly_10033_: *mut leanh::LeanObject,
    mut v_skipConstInApp_10034_: *mut leanh::LeanObject,
    mut v_skipInstances_10035_: *mut leanh::LeanObject,
    mut v_fvars_10036_: *mut leanh::LeanObject,
    mut v_e_10037_: *mut leanh::LeanObject,
    mut v_a_10038_: *mut leanh::LeanObject,
    mut v___y_10039_: *mut leanh::LeanObject,
    mut v___y_10040_: *mut leanh::LeanObject,
    mut v___y_10041_: *mut leanh::LeanObject,
    mut v___y_10042_: *mut leanh::LeanObject,
    mut v___y_10043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_10044_: u8 = 0;
    let mut v_skipConstInApp_boxed_10045_: u8 = 0;
    let mut v_skipInstances_boxed_10046_: u8 = 0;
    let mut v_res_10047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_10044_ = (leanh::lean_unbox(v_usedLetOnly_10033_) as u8);
    v_skipConstInApp_boxed_10045_ = (leanh::lean_unbox(v_skipConstInApp_10034_) as u8);
    v_skipInstances_boxed_10046_ = (leanh::lean_unbox(v_skipInstances_10035_) as u8);
    v_res_10047_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_10031_, v_post_10032_, v_usedLetOnly_boxed_10044_, v_skipConstInApp_boxed_10045_, v_skipInstances_boxed_10046_, v_fvars_10036_, v_e_10037_, v_a_10038_, v___y_10039_, v___y_10040_, v___y_10041_, v___y_10042_);
    leanh::lean_dec(v___y_10042_);
    leanh::lean_dec_ref(v___y_10041_);
    leanh::lean_dec(v___y_10040_);
    leanh::lean_dec_ref(v___y_10039_);
    leanh::lean_dec(v_a_10038_);
    return v_res_10047_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___boxed(
    mut v_upperBound_10048_: *mut leanh::LeanObject,
    mut v___x_10049_: *mut leanh::LeanObject,
    mut v_pre_10050_: *mut leanh::LeanObject,
    mut v_post_10051_: *mut leanh::LeanObject,
    mut v_usedLetOnly_10052_: *mut leanh::LeanObject,
    mut v_skipConstInApp_10053_: *mut leanh::LeanObject,
    mut v_skipInstances_10054_: *mut leanh::LeanObject,
    mut v_a_10055_: *mut leanh::LeanObject,
    mut v_b_10056_: *mut leanh::LeanObject,
    mut v___y_10057_: *mut leanh::LeanObject,
    mut v___y_10058_: *mut leanh::LeanObject,
    mut v___y_10059_: *mut leanh::LeanObject,
    mut v___y_10060_: *mut leanh::LeanObject,
    mut v___y_10061_: *mut leanh::LeanObject,
    mut v___y_10062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_10063_: u8 = 0;
    let mut v_skipConstInApp_boxed_10064_: u8 = 0;
    let mut v_skipInstances_boxed_10065_: u8 = 0;
    let mut v_res_10066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_10063_ = (leanh::lean_unbox(v_usedLetOnly_10052_) as u8);
    v_skipConstInApp_boxed_10064_ = (leanh::lean_unbox(v_skipConstInApp_10053_) as u8);
    v_skipInstances_boxed_10065_ = (leanh::lean_unbox(v_skipInstances_10054_) as u8);
    v_res_10066_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_10048_, v___x_10049_, v_pre_10050_, v_post_10051_, v_usedLetOnly_boxed_10063_, v_skipConstInApp_boxed_10064_, v_skipInstances_boxed_10065_, v_a_10055_, v_b_10056_, v___y_10057_, v___y_10058_, v___y_10059_, v___y_10060_, v___y_10061_);
    leanh::lean_dec(v___y_10061_);
    leanh::lean_dec_ref(v___y_10060_);
    leanh::lean_dec(v___y_10059_);
    leanh::lean_dec_ref(v___y_10058_);
    leanh::lean_dec(v___y_10057_);
    leanh::lean_dec_ref(v___x_10049_);
    leanh::lean_dec(v_upperBound_10048_);
    return v_res_10066_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8___boxed(
    mut v_skipInstances_10067_: *mut leanh::LeanObject,
    mut v_pre_10068_: *mut leanh::LeanObject,
    mut v_post_10069_: *mut leanh::LeanObject,
    mut v_usedLetOnly_10070_: *mut leanh::LeanObject,
    mut v_skipConstInApp_10071_: *mut leanh::LeanObject,
    mut v_x_10072_: *mut leanh::LeanObject,
    mut v_x_10073_: *mut leanh::LeanObject,
    mut v_x_10074_: *mut leanh::LeanObject,
    mut v___y_10075_: *mut leanh::LeanObject,
    mut v___y_10076_: *mut leanh::LeanObject,
    mut v___y_10077_: *mut leanh::LeanObject,
    mut v___y_10078_: *mut leanh::LeanObject,
    mut v___y_10079_: *mut leanh::LeanObject,
    mut v___y_10080_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipInstances_boxed_10081_: u8 = 0;
    let mut v_usedLetOnly_boxed_10082_: u8 = 0;
    let mut v_skipConstInApp_boxed_10083_: u8 = 0;
    let mut v_res_10084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_skipInstances_boxed_10081_ = (leanh::lean_unbox(v_skipInstances_10067_) as u8);
    v_usedLetOnly_boxed_10082_ = (leanh::lean_unbox(v_usedLetOnly_10070_) as u8);
    v_skipConstInApp_boxed_10083_ = (leanh::lean_unbox(v_skipConstInApp_10071_) as u8);
    v_res_10084_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_boxed_10081_, v_pre_10068_, v_post_10069_, v_usedLetOnly_boxed_10082_, v_skipConstInApp_boxed_10083_, v_x_10072_, v_x_10073_, v_x_10074_, v___y_10075_, v___y_10076_, v___y_10077_, v___y_10078_, v___y_10079_);
    leanh::lean_dec(v___y_10079_);
    leanh::lean_dec_ref(v___y_10078_);
    leanh::lean_dec(v___y_10077_);
    leanh::lean_dec_ref(v___y_10076_);
    leanh::lean_dec(v___y_10075_);
    return v_res_10084_;
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(
    mut v_input_10085_: *mut leanh::LeanObject,
    mut v_pre_10086_: *mut leanh::LeanObject,
    mut v_post_10087_: *mut leanh::LeanObject,
    mut v_usedLetOnly_10088_: u8,
    mut v_skipConstInApp_10089_: u8,
    mut v___y_10090_: *mut leanh::LeanObject,
    mut v___y_10091_: *mut leanh::LeanObject,
    mut v___y_10092_: *mut leanh::LeanObject,
    mut v___y_10093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_10097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10098_: u8 = 0;
    let mut v___x_10099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_10100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_10105_: u8 = 0;
    let mut v___x_10107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10109_: u8 = 0;
    let mut v_unused_10110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10095_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Core_transform___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Core_transform___redArg___closed__2_once),
                    _init_l_Lean_Core_transform___redArg___closed__2,
                );
                v___x_10096_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(
                    leanh::lean_box(0),
                    v___x_10095_,
                    v___y_10090_,
                    v___y_10091_,
                    v___y_10092_,
                    v___y_10093_,
                );
                v_a_10097_ = leanh::lean_ctor_get(v___x_10096_, 0);
                leanh::lean_inc(v_a_10097_);
                leanh::lean_dec_ref(v___x_10096_);
                v___x_10098_ = 0;
                v___x_10099_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_10086_, v_post_10087_, v_usedLetOnly_10088_, v_skipConstInApp_10089_, v___x_10098_, v_input_10085_, v_a_10097_, v___y_10090_, v___y_10091_, v___y_10092_, v___y_10093_);
                if leanh::lean_obj_tag(v___x_10099_) == 0 {
                    v_a_10100_ = leanh::lean_ctor_get(v___x_10099_, 0);
                    leanh::lean_inc(v_a_10100_);
                    leanh::lean_dec_ref_known(v___x_10099_, 1);
                    v___x_10101_ = leanh::lean_alloc_closure(
                        l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___x_10101_, 0, leanh::lean_box(0));
                    leanh::lean_closure_set(v___x_10101_, 1, leanh::lean_box(0));
                    leanh::lean_closure_set(v___x_10101_, 2, v_a_10097_);
                    v___x_10102_ =
                        l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(
                            leanh::lean_box(0),
                            v___x_10101_,
                            v___y_10090_,
                            v___y_10091_,
                            v___y_10092_,
                            v___y_10093_,
                        );
                    v_isSharedCheck_10109_ = (!leanh::lean_is_exclusive(v___x_10102_)) as u8;
                    if v_isSharedCheck_10109_ == 0 {
                        v_unused_10110_ = leanh::lean_ctor_get(v___x_10102_, 0);
                        leanh::lean_dec(v_unused_10110_);
                        v___x_10104_ = v___x_10102_;
                        v_isShared_10105_ = v_isSharedCheck_10109_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_10102_);
                        v___x_10104_ = leanh::lean_box(0);
                        v_isShared_10105_ = v_isSharedCheck_10109_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_10097_);
                    return v___x_10099_;
                }
            }
            1 => {
                if v_isShared_10105_ == 0 {
                    leanh::lean_ctor_set(v___x_10104_, 0, v_a_10100_);
                    v___x_10107_ = v___x_10104_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10108_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10108_, 0, v_a_10100_);
                    v___x_10107_ = v_reuseFailAlloc_10108_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_10107_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___boxed(
    mut v_input_10111_: *mut leanh::LeanObject,
    mut v_pre_10112_: *mut leanh::LeanObject,
    mut v_post_10113_: *mut leanh::LeanObject,
    mut v_usedLetOnly_10114_: *mut leanh::LeanObject,
    mut v_skipConstInApp_10115_: *mut leanh::LeanObject,
    mut v___y_10116_: *mut leanh::LeanObject,
    mut v___y_10117_: *mut leanh::LeanObject,
    mut v___y_10118_: *mut leanh::LeanObject,
    mut v___y_10119_: *mut leanh::LeanObject,
    mut v___y_10120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_10121_: u8 = 0;
    let mut v_skipConstInApp_boxed_10122_: u8 = 0;
    let mut v_res_10123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_10121_ = (leanh::lean_unbox(v_usedLetOnly_10114_) as u8);
    v_skipConstInApp_boxed_10122_ = (leanh::lean_unbox(v_skipConstInApp_10115_) as u8);
    v_res_10123_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(
        v_input_10111_,
        v_pre_10112_,
        v_post_10113_,
        v_usedLetOnly_boxed_10121_,
        v_skipConstInApp_boxed_10122_,
        v___y_10116_,
        v___y_10117_,
        v___y_10118_,
        v___y_10119_,
    );
    leanh::lean_dec(v___y_10119_);
    leanh::lean_dec_ref(v___y_10118_);
    leanh::lean_dec(v___y_10117_);
    leanh::lean_dec_ref(v___y_10116_);
    return v_res_10123_;
}
pub unsafe fn l_Lean_Meta_zetaReduce(
    mut v_e_10125_: *mut leanh::LeanObject,
    mut v_zetaDelta_10126_: u8,
    mut v_zetaHave_10127_: u8,
    mut v_beta_10128_: u8,
    mut v_a_10129_: *mut leanh::LeanObject,
    mut v_a_10130_: *mut leanh::LeanObject,
    mut v_a_10131_: *mut leanh::LeanObject,
    mut v_a_10132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lctx_10134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_10138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10139_: u8 = 0;
    v_lctx_10134_ = leanh::lean_ctor_get(v_a_10129_, 2);
    leanh::lean_inc_ref(v_lctx_10134_);
    v___x_10135_ = lean_local_ctx_num_indices(v_lctx_10134_);
    v___x_10136_ = leanh::lean_box((v_zetaHave_10127_) as usize);
    v___x_10137_ = leanh::lean_box((v_zetaDelta_10126_) as usize);
    v___f_10138_ = leanh::lean_alloc_closure(
        l_Lean_Meta_zetaReduce___lam__0___boxed as *mut core::ffi::c_void,
        9,
        3,
    );
    leanh::lean_closure_set(v___f_10138_, 0, v___x_10136_);
    leanh::lean_closure_set(v___f_10138_, 1, v___x_10135_);
    leanh::lean_closure_set(v___f_10138_, 2, v___x_10137_);
    v___x_10139_ = 1;
    if v_beta_10128_ == 0 {
        let mut v___f_10140_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_10141_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_10142_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_10140_ = l_Lean_Meta_zetaReduce___closed__0;
        v___f_10141_ = leanh::lean_alloc_closure(
            l_Lean_Meta_zetaReduce___lam__2___boxed as *mut core::ffi::c_void,
            7,
            1,
        );
        leanh::lean_closure_set(v___f_10141_, 0, v___f_10138_);
        v___x_10142_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(
            v_e_10125_,
            v___f_10141_,
            v___f_10140_,
            v___x_10139_,
            v_beta_10128_,
            v_a_10129_,
            v_a_10130_,
            v_a_10131_,
            v_a_10132_,
        );
        return v___x_10142_;
    } else {
        let mut v___f_10143_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_10144_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_10145_: u8 = 0;
        let mut v___x_10146_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_10143_ = l_Lean_Meta_zetaReduce___closed__0;
        v___f_10144_ = leanh::lean_alloc_closure(
            l_Lean_Meta_zetaReduce___lam__4___boxed as *mut core::ffi::c_void,
            7,
            1,
        );
        leanh::lean_closure_set(v___f_10144_, 0, v___f_10138_);
        v___x_10145_ = 0;
        v___x_10146_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(
            v_e_10125_,
            v___f_10144_,
            v___f_10143_,
            v___x_10139_,
            v___x_10145_,
            v_a_10129_,
            v_a_10130_,
            v_a_10131_,
            v_a_10132_,
        );
        return v___x_10146_;
    }
}
pub unsafe fn l_Lean_Meta_zetaReduce___boxed(
    mut v_e_10147_: *mut leanh::LeanObject,
    mut v_zetaDelta_10148_: *mut leanh::LeanObject,
    mut v_zetaHave_10149_: *mut leanh::LeanObject,
    mut v_beta_10150_: *mut leanh::LeanObject,
    mut v_a_10151_: *mut leanh::LeanObject,
    mut v_a_10152_: *mut leanh::LeanObject,
    mut v_a_10153_: *mut leanh::LeanObject,
    mut v_a_10154_: *mut leanh::LeanObject,
    mut v_a_10155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zetaDelta_boxed_10156_: u8 = 0;
    let mut v_zetaHave_boxed_10157_: u8 = 0;
    let mut v_beta_boxed_10158_: u8 = 0;
    let mut v_res_10159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_zetaDelta_boxed_10156_ = (leanh::lean_unbox(v_zetaDelta_10148_) as u8);
    v_zetaHave_boxed_10157_ = (leanh::lean_unbox(v_zetaHave_10149_) as u8);
    v_beta_boxed_10158_ = (leanh::lean_unbox(v_beta_10150_) as u8);
    v_res_10159_ = l_Lean_Meta_zetaReduce(
        v_e_10147_,
        v_zetaDelta_boxed_10156_,
        v_zetaHave_boxed_10157_,
        v_beta_boxed_10158_,
        v_a_10151_,
        v_a_10152_,
        v_a_10153_,
        v_a_10154_,
    );
    leanh::lean_dec(v_a_10154_);
    leanh::lean_dec_ref(v_a_10153_);
    leanh::lean_dec(v_a_10152_);
    leanh::lean_dec_ref(v_a_10151_);
    return v_res_10159_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(
    mut v_upperBound_10160_: *mut leanh::LeanObject,
    mut v___x_10161_: *mut leanh::LeanObject,
    mut v_pre_10162_: *mut leanh::LeanObject,
    mut v_post_10163_: *mut leanh::LeanObject,
    mut v_usedLetOnly_10164_: u8,
    mut v_skipConstInApp_10165_: u8,
    mut v_skipInstances_10166_: u8,
    mut v___x_10167_: *mut leanh::LeanObject,
    mut v_inst_10168_: *mut leanh::LeanObject,
    mut v_R_10169_: *mut leanh::LeanObject,
    mut v_a_10170_: *mut leanh::LeanObject,
    mut v_b_10171_: *mut leanh::LeanObject,
    mut v_c_10172_: *mut leanh::LeanObject,
    mut v___y_10173_: *mut leanh::LeanObject,
    mut v___y_10174_: *mut leanh::LeanObject,
    mut v___y_10175_: *mut leanh::LeanObject,
    mut v___y_10176_: *mut leanh::LeanObject,
    mut v___y_10177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10179_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_10160_, v___x_10161_, v_pre_10162_, v_post_10163_, v_usedLetOnly_10164_, v_skipConstInApp_10165_, v_skipInstances_10166_, v_a_10170_, v_b_10171_, v___y_10173_, v___y_10174_, v___y_10175_, v___y_10176_, v___y_10177_);
    return v___x_10179_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_upperBound_10180_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___x_10181_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_pre_10182_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_post_10183_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_usedLetOnly_10184_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_skipConstInApp_10185_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_skipInstances_10186_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_10187_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_inst_10188_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_R_10189_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_a_10190_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_b_10191_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_c_10192_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_10193_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_10194_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_10195_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_10196_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_10197_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___y_10198_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_usedLetOnly_boxed_10199_: u8 = 0;
    let mut v_skipConstInApp_boxed_10200_: u8 = 0;
    let mut v_skipInstances_boxed_10201_: u8 = 0;
    let mut v_res_10202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_10199_ = (leanh::lean_unbox(v_usedLetOnly_10184_) as u8);
    v_skipConstInApp_boxed_10200_ = (leanh::lean_unbox(v_skipConstInApp_10185_) as u8);
    v_skipInstances_boxed_10201_ = (leanh::lean_unbox(v_skipInstances_10186_) as u8);
    v_res_10202_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(v_upperBound_10180_, v___x_10181_, v_pre_10182_, v_post_10183_, v_usedLetOnly_boxed_10199_, v_skipConstInApp_boxed_10200_, v_skipInstances_boxed_10201_, v___x_10187_, v_inst_10188_, v_R_10189_, v_a_10190_, v_b_10191_, v_c_10192_, v___y_10193_, v___y_10194_, v___y_10195_, v___y_10196_, v___y_10197_);
    leanh::lean_dec(v___y_10197_);
    leanh::lean_dec_ref(v___y_10196_);
    leanh::lean_dec(v___y_10195_);
    leanh::lean_dec_ref(v___y_10194_);
    leanh::lean_dec(v___y_10193_);
    leanh::lean_dec(v___x_10187_);
    leanh::lean_dec_ref(v___x_10181_);
    leanh::lean_dec(v_upperBound_10180_);
    return v_res_10202_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(
    mut v_00_u03b1_10203_: *mut leanh::LeanObject,
    mut v_name_10204_: *mut leanh::LeanObject,
    mut v_bi_10205_: u8,
    mut v_type_10206_: *mut leanh::LeanObject,
    mut v_k_10207_: *mut leanh::LeanObject,
    mut v_kind_10208_: u8,
    mut v___y_10209_: *mut leanh::LeanObject,
    mut v___y_10210_: *mut leanh::LeanObject,
    mut v___y_10211_: *mut leanh::LeanObject,
    mut v___y_10212_: *mut leanh::LeanObject,
    mut v___y_10213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10215_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_10204_, v_bi_10205_, v_type_10206_, v_k_10207_, v_kind_10208_, v___y_10209_, v___y_10210_, v___y_10211_, v___y_10212_, v___y_10213_);
    return v___x_10215_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___boxed(
    mut v_00_u03b1_10216_: *mut leanh::LeanObject,
    mut v_name_10217_: *mut leanh::LeanObject,
    mut v_bi_10218_: *mut leanh::LeanObject,
    mut v_type_10219_: *mut leanh::LeanObject,
    mut v_k_10220_: *mut leanh::LeanObject,
    mut v_kind_10221_: *mut leanh::LeanObject,
    mut v___y_10222_: *mut leanh::LeanObject,
    mut v___y_10223_: *mut leanh::LeanObject,
    mut v___y_10224_: *mut leanh::LeanObject,
    mut v___y_10225_: *mut leanh::LeanObject,
    mut v___y_10226_: *mut leanh::LeanObject,
    mut v___y_10227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_10228_: u8 = 0;
    let mut v_kind_boxed_10229_: u8 = 0;
    let mut v_res_10230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_10228_ = (leanh::lean_unbox(v_bi_10218_) as u8);
    v_kind_boxed_10229_ = (leanh::lean_unbox(v_kind_10221_) as u8);
    v_res_10230_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b1_10216_, v_name_10217_, v_bi_boxed_10228_, v_type_10219_, v_k_10220_, v_kind_boxed_10229_, v___y_10222_, v___y_10223_, v___y_10224_, v___y_10225_, v___y_10226_);
    leanh::lean_dec(v___y_10226_);
    leanh::lean_dec_ref(v___y_10225_);
    leanh::lean_dec(v___y_10224_);
    leanh::lean_dec_ref(v___y_10223_);
    leanh::lean_dec(v___y_10222_);
    return v_res_10230_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(
    mut v_00_u03b1_10231_: *mut leanh::LeanObject,
    mut v_name_10232_: *mut leanh::LeanObject,
    mut v_type_10233_: *mut leanh::LeanObject,
    mut v_val_10234_: *mut leanh::LeanObject,
    mut v_k_10235_: *mut leanh::LeanObject,
    mut v_nondep_10236_: u8,
    mut v_kind_10237_: u8,
    mut v___y_10238_: *mut leanh::LeanObject,
    mut v___y_10239_: *mut leanh::LeanObject,
    mut v___y_10240_: *mut leanh::LeanObject,
    mut v___y_10241_: *mut leanh::LeanObject,
    mut v___y_10242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10244_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_10232_, v_type_10233_, v_val_10234_, v_k_10235_, v_nondep_10236_, v_kind_10237_, v___y_10238_, v___y_10239_, v___y_10240_, v___y_10241_, v___y_10242_);
    return v___x_10244_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___boxed(
    mut v_00_u03b1_10245_: *mut leanh::LeanObject,
    mut v_name_10246_: *mut leanh::LeanObject,
    mut v_type_10247_: *mut leanh::LeanObject,
    mut v_val_10248_: *mut leanh::LeanObject,
    mut v_k_10249_: *mut leanh::LeanObject,
    mut v_nondep_10250_: *mut leanh::LeanObject,
    mut v_kind_10251_: *mut leanh::LeanObject,
    mut v___y_10252_: *mut leanh::LeanObject,
    mut v___y_10253_: *mut leanh::LeanObject,
    mut v___y_10254_: *mut leanh::LeanObject,
    mut v___y_10255_: *mut leanh::LeanObject,
    mut v___y_10256_: *mut leanh::LeanObject,
    mut v___y_10257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_nondep_boxed_10258_: u8 = 0;
    let mut v_kind_boxed_10259_: u8 = 0;
    let mut v_res_10260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_10258_ = (leanh::lean_unbox(v_nondep_10250_) as u8);
    v_kind_boxed_10259_ = (leanh::lean_unbox(v_kind_10251_) as u8);
    v_res_10260_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(v_00_u03b1_10245_, v_name_10246_, v_type_10247_, v_val_10248_, v_k_10249_, v_nondep_boxed_10258_, v_kind_boxed_10259_, v___y_10252_, v___y_10253_, v___y_10254_, v___y_10255_, v___y_10256_);
    leanh::lean_dec(v___y_10256_);
    leanh::lean_dec_ref(v___y_10255_);
    leanh::lean_dec(v___y_10254_);
    leanh::lean_dec_ref(v___y_10253_);
    leanh::lean_dec(v___y_10252_);
    return v_res_10260_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(
    mut v_00_u03b1_10261_: *mut leanh::LeanObject,
    mut v_ref_10262_: *mut leanh::LeanObject,
    mut v___y_10263_: *mut leanh::LeanObject,
    mut v___y_10264_: *mut leanh::LeanObject,
    mut v___y_10265_: *mut leanh::LeanObject,
    mut v___y_10266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10268_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_10262_);
    return v___x_10268_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___boxed(
    mut v_00_u03b1_10269_: *mut leanh::LeanObject,
    mut v_ref_10270_: *mut leanh::LeanObject,
    mut v___y_10271_: *mut leanh::LeanObject,
    mut v___y_10272_: *mut leanh::LeanObject,
    mut v___y_10273_: *mut leanh::LeanObject,
    mut v___y_10274_: *mut leanh::LeanObject,
    mut v___y_10275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_10276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_10276_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(v_00_u03b1_10269_, v_ref_10270_, v___y_10271_, v___y_10272_, v___y_10273_, v___y_10274_);
    leanh::lean_dec(v___y_10274_);
    leanh::lean_dec_ref(v___y_10273_);
    leanh::lean_dec(v___y_10272_);
    leanh::lean_dec_ref(v___y_10271_);
    return v_res_10276_;
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(
    mut v_00_u03b1_10277_: *mut leanh::LeanObject,
    mut v_x_10278_: *mut leanh::LeanObject,
    mut v___y_10279_: *mut leanh::LeanObject,
    mut v___y_10280_: *mut leanh::LeanObject,
    mut v___y_10281_: *mut leanh::LeanObject,
    mut v___y_10282_: *mut leanh::LeanObject,
    mut v___y_10283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10285_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_10278_, v___y_10279_, v___y_10280_, v___y_10281_, v___y_10282_, v___y_10283_);
    return v___x_10285_;
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___boxed(
    mut v_00_u03b1_10286_: *mut leanh::LeanObject,
    mut v_x_10287_: *mut leanh::LeanObject,
    mut v___y_10288_: *mut leanh::LeanObject,
    mut v___y_10289_: *mut leanh::LeanObject,
    mut v___y_10290_: *mut leanh::LeanObject,
    mut v___y_10291_: *mut leanh::LeanObject,
    mut v___y_10292_: *mut leanh::LeanObject,
    mut v___y_10293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_10294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_10294_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(v_00_u03b1_10286_, v_x_10287_, v___y_10288_, v___y_10289_, v___y_10290_, v___y_10291_, v___y_10292_);
    leanh::lean_dec(v___y_10292_);
    leanh::lean_dec_ref(v___y_10291_);
    leanh::lean_dec(v___y_10290_);
    leanh::lean_dec_ref(v___y_10289_);
    leanh::lean_dec(v___y_10288_);
    return v_res_10294_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(
    mut v_a_10295_: *mut leanh::LeanObject,
    mut v_as_10296_: *mut leanh::LeanObject,
    mut v_i_10297_: usize,
    mut v_stop_10298_: usize,
) -> u8 {
    let mut v___x_10299_: u8 = 0;
    let mut v___x_10300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10301_: u8 = 0;
    let mut v___x_10302_: usize = 0;
    let mut v___x_10303_: usize = 0;
    let mut v___x_10305_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10299_ = lean_usize_dec_eq(v_i_10297_, v_stop_10298_);
                if v___x_10299_ == 0 {
                    v___x_10300_ = lean_array_uget_borrowed(v_as_10296_, v_i_10297_);
                    v___x_10301_ = l_Lean_instBEqFVarId_beq(v_a_10295_, v___x_10300_);
                    if v___x_10301_ == 0 {
                        v___x_10302_ = 1usize;
                        v___x_10303_ = lean_usize_add(v_i_10297_, v___x_10302_);
                        v_i_10297_ = v___x_10303_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_10301_;
                    }
                } else {
                    v___x_10305_ = 0;
                    return v___x_10305_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0___boxed(
    mut v_a_10306_: *mut leanh::LeanObject,
    mut v_as_10307_: *mut leanh::LeanObject,
    mut v_i_10308_: *mut leanh::LeanObject,
    mut v_stop_10309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_10310_: usize = 0;
    let mut v_stop_boxed_10311_: usize = 0;
    let mut v_res_10312_: u8 = 0;
    let mut v_r_10313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_10310_ = leanh::lean_unbox_usize(v_i_10308_);
    leanh::lean_dec(v_i_10308_);
    v_stop_boxed_10311_ = leanh::lean_unbox_usize(v_stop_10309_);
    leanh::lean_dec(v_stop_10309_);
    v_res_10312_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_10306_, v_as_10307_, v_i_boxed_10310_, v_stop_boxed_10311_);
    leanh::lean_dec_ref(v_as_10307_);
    leanh::lean_dec(v_a_10306_);
    v_r_10313_ = leanh::lean_box((v_res_10312_) as usize);
    return v_r_10313_;
}
pub unsafe fn l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(
    mut v_as_10314_: *mut leanh::LeanObject,
    mut v_a_10315_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_10316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10318_: u8 = 0;
    v___x_10316_ = leanh::lean_unsigned_to_nat(0);
    v___x_10317_ = lean_array_get_size(v_as_10314_);
    v___x_10318_ = lean_nat_dec_lt(v___x_10316_, v___x_10317_);
    if v___x_10318_ == 0 {
        return v___x_10318_;
    } else {
        if v___x_10318_ == 0 {
            return v___x_10318_;
        } else {
            let mut v___x_10319_: usize = 0;
            let mut v___x_10320_: usize = 0;
            let mut v___x_10321_: u8 = 0;
            v___x_10319_ = 0usize;
            v___x_10320_ = lean_usize_of_nat(v___x_10317_);
            v___x_10321_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_10315_, v_as_10314_, v___x_10319_, v___x_10320_);
            return v___x_10321_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0___boxed(
    mut v_as_10322_: *mut leanh::LeanObject,
    mut v_a_10323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_10324_: u8 = 0;
    let mut v_r_10325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_10324_ =
        l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_as_10322_, v_a_10323_);
    leanh::lean_dec(v_a_10323_);
    leanh::lean_dec_ref(v_as_10322_);
    v_r_10325_ = leanh::lean_box((v_res_10324_) as usize);
    return v_r_10325_;
}
pub unsafe fn l_Lean_Meta_zetaDeltaFVars___lam__1(
    mut v_fvars_10326_: *mut leanh::LeanObject,
    mut v_e_10327_: *mut leanh::LeanObject,
    mut v___y_10328_: *mut leanh::LeanObject,
    mut v___y_10329_: *mut leanh::LeanObject,
    mut v___y_10330_: *mut leanh::LeanObject,
    mut v___y_10331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_10337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10338_: u8 = 0;
    let mut v___x_10339_: u8 = 0;
    let mut v___x_10340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_10341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_10342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_10345_: u8 = 0;
    let mut v___x_10346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_10347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_10350_: u8 = 0;
    let mut v_dummy_10351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_10352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10364_: u8 = 0;
    let mut v_isSharedCheck_10365_: u8 = 0;
    let mut v_a_10366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_10369_: u8 = 0;
    let mut v___x_10371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10373_: u8 = 0;
    let mut v___x_10374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10336_ = l_Lean_Expr_getAppFn(v_e_10327_);
                if leanh::lean_obj_tag(v___x_10336_) == 1 {
                    v_fvarId_10337_ = leanh::lean_ctor_get(v___x_10336_, 0);
                    leanh::lean_inc(v_fvarId_10337_);
                    leanh::lean_dec_ref_known(v___x_10336_, 1);
                    v___x_10338_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(
                        v_fvars_10326_,
                        v_fvarId_10337_,
                    );
                    if v___x_10338_ == 0 {
                        leanh::lean_dec(v_fvarId_10337_);
                        leanh::lean_dec_ref(v_e_10327_);
                        state = 1;
                        continue;
                    } else {
                        v___x_10339_ = 0;
                        v___x_10340_ = l_Lean_FVarId_getValue_x3f___redArg(
                            v_fvarId_10337_,
                            v___x_10339_,
                            v___y_10328_,
                            v___y_10330_,
                            v___y_10331_,
                        );
                        if leanh::lean_obj_tag(v___x_10340_) == 0 {
                            v_a_10341_ = leanh::lean_ctor_get(v___x_10340_, 0);
                            leanh::lean_inc(v_a_10341_);
                            leanh::lean_dec_ref_known(v___x_10340_, 1);
                            if leanh::lean_obj_tag(v_a_10341_) == 1 {
                                v_val_10342_ = leanh::lean_ctor_get(v_a_10341_, 0);
                                v_isSharedCheck_10365_ =
                                    (!leanh::lean_is_exclusive(v_a_10341_)) as u8;
                                if v_isSharedCheck_10365_ == 0 {
                                    v___x_10344_ = v_a_10341_;
                                    v_isShared_10345_ = v_isSharedCheck_10365_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_10342_);
                                    leanh::lean_dec(v_a_10341_);
                                    v___x_10344_ = leanh::lean_box(0);
                                    v_isShared_10345_ = v_isSharedCheck_10365_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_10341_);
                                leanh::lean_dec_ref(v_e_10327_);
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_e_10327_);
                            v_a_10366_ = leanh::lean_ctor_get(v___x_10340_, 0);
                            v_isSharedCheck_10373_ =
                                (!leanh::lean_is_exclusive(v___x_10340_)) as u8;
                            if v_isSharedCheck_10373_ == 0 {
                                v___x_10368_ = v___x_10340_;
                                v_isShared_10369_ = v_isSharedCheck_10373_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_10366_);
                                leanh::lean_dec(v___x_10340_);
                                v___x_10368_ = leanh::lean_box(0);
                                v_isShared_10369_ = v_isSharedCheck_10373_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_10336_);
                    leanh::lean_dec_ref(v_e_10327_);
                    v___x_10374_ = l_Lean_Core_betaReduce___lam__0___closed__0;
                    v___x_10375_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_10375_, 0, v___x_10374_);
                    return v___x_10375_;
                }
            }
            1 => {
                v___x_10334_ = l_Lean_Core_betaReduce___lam__0___closed__0;
                v___x_10335_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_10335_, 0, v___x_10334_);
                return v___x_10335_;
            }
            2 => {
                v___x_10346_ =
                    l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(
                        v_val_10342_,
                        v___y_10329_,
                    );
                v_a_10347_ = leanh::lean_ctor_get(v___x_10346_, 0);
                v_isSharedCheck_10364_ = (!leanh::lean_is_exclusive(v___x_10346_)) as u8;
                if v_isSharedCheck_10364_ == 0 {
                    v___x_10349_ = v___x_10346_;
                    v_isShared_10350_ = v_isSharedCheck_10364_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_a_10347_);
                    leanh::lean_dec(v___x_10346_);
                    v___x_10349_ = leanh::lean_box(0);
                    v_isShared_10350_ = v_isSharedCheck_10364_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_dummy_10351_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once), _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
                v_nargs_10352_ = l_Lean_Expr_getAppNumArgs(v_e_10327_);
                leanh::lean_inc(v_nargs_10352_);
                v___x_10353_ = lean_mk_array(v_nargs_10352_, v_dummy_10351_);
                v___x_10354_ = leanh::lean_unsigned_to_nat(1);
                v___x_10355_ = lean_nat_sub(v_nargs_10352_, v___x_10354_);
                leanh::lean_dec(v_nargs_10352_);
                v___x_10356_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_e_10327_,
                    v___x_10353_,
                    v___x_10355_,
                );
                v___x_10357_ = l_Lean_Expr_beta(v_a_10347_, v___x_10356_);
                if v_isShared_10345_ == 0 {
                    leanh::lean_ctor_set(v___x_10344_, 0, v___x_10357_);
                    v___x_10359_ = v___x_10344_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_10363_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10363_, 0, v___x_10357_);
                    v___x_10359_ = v_reuseFailAlloc_10363_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_10350_ == 0 {
                    leanh::lean_ctor_set(v___x_10349_, 0, v___x_10359_);
                    v___x_10361_ = v___x_10349_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_10362_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10362_, 0, v___x_10359_);
                    v___x_10361_ = v_reuseFailAlloc_10362_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_10361_;
            }
            6 => {
                if v_isShared_10369_ == 0 {
                    v___x_10371_ = v___x_10368_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_10372_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10372_, 0, v_a_10366_);
                    v___x_10371_ = v_reuseFailAlloc_10372_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_10371_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_zetaDeltaFVars___lam__1___boxed(
    mut v_fvars_10376_: *mut leanh::LeanObject,
    mut v_e_10377_: *mut leanh::LeanObject,
    mut v___y_10378_: *mut leanh::LeanObject,
    mut v___y_10379_: *mut leanh::LeanObject,
    mut v___y_10380_: *mut leanh::LeanObject,
    mut v___y_10381_: *mut leanh::LeanObject,
    mut v___y_10382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_10383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_10383_ = l_Lean_Meta_zetaDeltaFVars___lam__1(
        v_fvars_10376_,
        v_e_10377_,
        v___y_10378_,
        v___y_10379_,
        v___y_10380_,
        v___y_10381_,
    );
    leanh::lean_dec(v___y_10381_);
    leanh::lean_dec_ref(v___y_10380_);
    leanh::lean_dec(v___y_10379_);
    leanh::lean_dec_ref(v___y_10378_);
    leanh::lean_dec_ref(v_fvars_10376_);
    return v_res_10383_;
}
pub unsafe fn l_Lean_Meta_zetaDeltaFVars(
    mut v_e_10384_: *mut leanh::LeanObject,
    mut v_fvars_10385_: *mut leanh::LeanObject,
    mut v_a_10386_: *mut leanh::LeanObject,
    mut v_a_10387_: *mut leanh::LeanObject,
    mut v_a_10388_: *mut leanh::LeanObject,
    mut v_a_10389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_10391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_10392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10393_: u8 = 0;
    let mut v___x_10394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_10391_ = l_Lean_Meta_zetaReduce___closed__0;
    v_pre_10392_ = leanh::lean_alloc_closure(
        l_Lean_Meta_zetaDeltaFVars___lam__1___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    leanh::lean_closure_set(v_pre_10392_, 0, v_fvars_10385_);
    v___x_10393_ = 0;
    v___x_10394_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(
        v_e_10384_,
        v_pre_10392_,
        v___f_10391_,
        v___x_10393_,
        v___x_10393_,
        v_a_10386_,
        v_a_10387_,
        v_a_10388_,
        v_a_10389_,
    );
    return v___x_10394_;
}
pub unsafe fn l_Lean_Meta_zetaDeltaFVars___boxed(
    mut v_e_10395_: *mut leanh::LeanObject,
    mut v_fvars_10396_: *mut leanh::LeanObject,
    mut v_a_10397_: *mut leanh::LeanObject,
    mut v_a_10398_: *mut leanh::LeanObject,
    mut v_a_10399_: *mut leanh::LeanObject,
    mut v_a_10400_: *mut leanh::LeanObject,
    mut v_a_10401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_10402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_10402_ = l_Lean_Meta_zetaDeltaFVars(
        v_e_10395_,
        v_fvars_10396_,
        v_a_10397_,
        v_a_10398_,
        v_a_10399_,
        v_a_10400_,
    );
    leanh::lean_dec(v_a_10400_);
    leanh::lean_dec_ref(v_a_10399_);
    leanh::lean_dec(v_a_10398_);
    leanh::lean_dec_ref(v_a_10397_);
    return v_res_10402_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_10403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10403_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_10403_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_10404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10404_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0_once
        ),
        _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0,
    );
    v___x_10405_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_10405_, 0, v___x_10404_);
    return v___x_10405_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_10406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10406_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1_once
        ),
        _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1,
    );
    v___x_10407_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_10407_, 0, v___x_10406_);
    leanh::lean_ctor_set(v___x_10407_, 1, v___x_10406_);
    return v___x_10407_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(
    mut v_env_10408_: *mut leanh::LeanObject,
    mut v___y_10409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_10412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_10413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_10414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_10415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_10416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_10417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_10418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_10421_: u8 = 0;
    let mut v___x_10422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10429_: u8 = 0;
    let mut v_unused_10430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_10431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10411_ = lean_st_ref_take(v___y_10409_);
                v_nextMacroScope_10412_ = leanh::lean_ctor_get(v___x_10411_, 1);
                v_ngen_10413_ = leanh::lean_ctor_get(v___x_10411_, 2);
                v_auxDeclNGen_10414_ = leanh::lean_ctor_get(v___x_10411_, 3);
                v_traceState_10415_ = leanh::lean_ctor_get(v___x_10411_, 4);
                v_messages_10416_ = leanh::lean_ctor_get(v___x_10411_, 6);
                v_infoState_10417_ = leanh::lean_ctor_get(v___x_10411_, 7);
                v_snapshotTasks_10418_ = leanh::lean_ctor_get(v___x_10411_, 8);
                v_isSharedCheck_10429_ = (!leanh::lean_is_exclusive(v___x_10411_)) as u8;
                if v_isSharedCheck_10429_ == 0 {
                    v_unused_10430_ = leanh::lean_ctor_get(v___x_10411_, 5);
                    leanh::lean_dec(v_unused_10430_);
                    v_unused_10431_ = leanh::lean_ctor_get(v___x_10411_, 0);
                    leanh::lean_dec(v_unused_10431_);
                    v___x_10420_ = v___x_10411_;
                    v_isShared_10421_ = v_isSharedCheck_10429_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_10418_);
                    leanh::lean_inc(v_infoState_10417_);
                    leanh::lean_inc(v_messages_10416_);
                    leanh::lean_inc(v_traceState_10415_);
                    leanh::lean_inc(v_auxDeclNGen_10414_);
                    leanh::lean_inc(v_ngen_10413_);
                    leanh::lean_inc(v_nextMacroScope_10412_);
                    leanh::lean_dec(v___x_10411_);
                    v___x_10420_ = leanh::lean_box(0);
                    v_isShared_10421_ = v_isSharedCheck_10429_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_10422_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once), _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
                if v_isShared_10421_ == 0 {
                    leanh::lean_ctor_set(v___x_10420_, 5, v___x_10422_);
                    leanh::lean_ctor_set(v___x_10420_, 0, v_env_10408_);
                    v___x_10424_ = v___x_10420_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10428_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10428_, 0, v_env_10408_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_10428_,
                        1,
                        v_nextMacroScope_10412_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_10428_, 2, v_ngen_10413_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10428_, 3, v_auxDeclNGen_10414_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10428_, 4, v_traceState_10415_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10428_, 5, v___x_10422_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10428_, 6, v_messages_10416_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10428_, 7, v_infoState_10417_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10428_, 8, v_snapshotTasks_10418_);
                    v___x_10424_ = v_reuseFailAlloc_10428_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_10425_ = lean_st_ref_set(v___y_10409_, v___x_10424_);
                v___x_10426_ = leanh::lean_box(0);
                v___x_10427_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_10427_, 0, v___x_10426_);
                return v___x_10427_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___boxed(
    mut v_env_10432_: *mut leanh::LeanObject,
    mut v___y_10433_: *mut leanh::LeanObject,
    mut v___y_10434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_10435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_10435_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(
        v_env_10432_,
        v___y_10433_,
    );
    leanh::lean_dec(v___y_10433_);
    return v_res_10435_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(
    mut v_env_10436_: *mut leanh::LeanObject,
    mut v___y_10437_: *mut leanh::LeanObject,
    mut v___y_10438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10440_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(
        v_env_10436_,
        v___y_10438_,
    );
    return v___x_10440_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___boxed(
    mut v_env_10441_: *mut leanh::LeanObject,
    mut v___y_10442_: *mut leanh::LeanObject,
    mut v___y_10443_: *mut leanh::LeanObject,
    mut v___y_10444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_10445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_10445_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(
        v_env_10441_,
        v___y_10442_,
        v___y_10443_,
    );
    leanh::lean_dec(v___y_10443_);
    leanh::lean_dec_ref(v___y_10442_);
    return v_res_10445_;
}
pub unsafe fn l_Lean_Meta_unfoldDeclsFrom___lam__1(
    mut v_env_10446_: *mut leanh::LeanObject,
    mut v___x_10447_: *mut leanh::LeanObject,
    mut v___x_10448_: u8,
    mut v_e_10449_: *mut leanh::LeanObject,
    mut v___y_10450_: *mut leanh::LeanObject,
    mut v___y_10451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_declName_10453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_10454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10455_: u8 = 0;
    let mut v___x_10456_: u8 = 0;
    let mut v___x_10457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_10458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_10461_: u8 = 0;
    let mut v___x_10462_: u8 = 0;
    let mut v___x_10464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_10468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_10471_: u8 = 0;
    let mut v___x_10473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10478_: u8 = 0;
    let mut v_a_10479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_10482_: u8 = 0;
    let mut v___x_10484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10486_: u8 = 0;
    let mut v_isSharedCheck_10487_: u8 = 0;
    let mut v___x_10488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_e_10449_) == 4 {
                    v_declName_10453_ = leanh::lean_ctor_get(v_e_10449_, 0);
                    v_us_10454_ = leanh::lean_ctor_get(v_e_10449_, 1);
                    v___x_10455_ = 1;
                    leanh::lean_inc(v_declName_10453_);
                    v___x_10456_ =
                        l_Lean_Environment_contains(v_env_10446_, v_declName_10453_, v___x_10455_);
                    if v___x_10456_ == 0 {
                        leanh::lean_inc(v_declName_10453_);
                        v___x_10457_ = l_Lean_Environment_find_x3f(
                            v___x_10447_,
                            v_declName_10453_,
                            v___x_10448_,
                        );
                        if leanh::lean_obj_tag(v___x_10457_) == 1 {
                            v_val_10458_ = leanh::lean_ctor_get(v___x_10457_, 0);
                            v_isSharedCheck_10487_ =
                                (!leanh::lean_is_exclusive(v___x_10457_)) as u8;
                            if v_isSharedCheck_10487_ == 0 {
                                v___x_10460_ = v___x_10457_;
                                v_isShared_10461_ = v_isSharedCheck_10487_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_10458_);
                                leanh::lean_dec(v___x_10457_);
                                v___x_10460_ = leanh::lean_box(0);
                                v_isShared_10461_ = v_isSharedCheck_10487_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_10457_);
                            v___x_10488_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_10488_, 0, v_e_10449_);
                            v___x_10489_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_10489_, 0, v___x_10488_);
                            return v___x_10489_;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_10447_);
                        v___x_10490_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_10490_, 0, v_e_10449_);
                        v___x_10491_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_10491_, 0, v___x_10490_);
                        return v___x_10491_;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_10449_);
                    leanh::lean_dec_ref(v___x_10447_);
                    leanh::lean_dec_ref(v_env_10446_);
                    v___x_10492_ = l_Lean_Core_betaReduce___lam__0___closed__0;
                    v___x_10493_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_10493_, 0, v___x_10492_);
                    return v___x_10493_;
                }
            }
            1 => {
                v___x_10462_ = l_Lean_ConstantInfo_hasValue(v_val_10458_, v___x_10455_);
                if v___x_10462_ == 0 {
                    leanh::lean_dec(v_val_10458_);
                    if v_isShared_10461_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_10460_, 0);
                        leanh::lean_ctor_set(v___x_10460_, 0, v_e_10449_);
                        v___x_10464_ = v___x_10460_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_10466_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_10466_, 0, v_e_10449_);
                        v___x_10464_ = v_reuseFailAlloc_10466_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_us_10454_);
                    leanh::lean_dec_ref_known(v_e_10449_, 2);
                    v___x_10467_ = l_Lean_Core_instantiateValueLevelParams(
                        v_val_10458_,
                        v_us_10454_,
                        v___x_10455_,
                        v___y_10450_,
                        v___y_10451_,
                    );
                    leanh::lean_dec(v_val_10458_);
                    if leanh::lean_obj_tag(v___x_10467_) == 0 {
                        v_a_10468_ = leanh::lean_ctor_get(v___x_10467_, 0);
                        v_isSharedCheck_10478_ =
                            (!leanh::lean_is_exclusive(v___x_10467_)) as u8;
                        if v_isSharedCheck_10478_ == 0 {
                            v___x_10470_ = v___x_10467_;
                            v_isShared_10471_ = v_isSharedCheck_10478_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_10468_);
                            leanh::lean_dec(v___x_10467_);
                            v___x_10470_ = leanh::lean_box(0);
                            v_isShared_10471_ = v_isSharedCheck_10478_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_10460_);
                        v_a_10479_ = leanh::lean_ctor_get(v___x_10467_, 0);
                        v_isSharedCheck_10486_ =
                            (!leanh::lean_is_exclusive(v___x_10467_)) as u8;
                        if v_isSharedCheck_10486_ == 0 {
                            v___x_10481_ = v___x_10467_;
                            v_isShared_10482_ = v_isSharedCheck_10486_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_10479_);
                            leanh::lean_dec(v___x_10467_);
                            v___x_10481_ = leanh::lean_box(0);
                            v_isShared_10482_ = v_isSharedCheck_10486_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_10465_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_10465_, 0, v___x_10464_);
                return v___x_10465_;
            }
            3 => {
                if v_isShared_10461_ == 0 {
                    leanh::lean_ctor_set(v___x_10460_, 0, v_a_10468_);
                    v___x_10473_ = v___x_10460_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_10477_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10477_, 0, v_a_10468_);
                    v___x_10473_ = v_reuseFailAlloc_10477_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_10471_ == 0 {
                    leanh::lean_ctor_set(v___x_10470_, 0, v___x_10473_);
                    v___x_10475_ = v___x_10470_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_10476_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10476_, 0, v___x_10473_);
                    v___x_10475_ = v_reuseFailAlloc_10476_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_10475_;
            }
            6 => {
                if v_isShared_10482_ == 0 {
                    v___x_10484_ = v___x_10481_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_10485_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10485_, 0, v_a_10479_);
                    v___x_10484_ = v_reuseFailAlloc_10485_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_10484_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed(
    mut v_env_10494_: *mut leanh::LeanObject,
    mut v___x_10495_: *mut leanh::LeanObject,
    mut v___x_10496_: *mut leanh::LeanObject,
    mut v_e_10497_: *mut leanh::LeanObject,
    mut v___y_10498_: *mut leanh::LeanObject,
    mut v___y_10499_: *mut leanh::LeanObject,
    mut v___y_10500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2152__boxed_10501_: u8 = 0;
    let mut v_res_10502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2152__boxed_10501_ = (leanh::lean_unbox(v___x_10496_) as u8);
    v_res_10502_ = l_Lean_Meta_unfoldDeclsFrom___lam__1(
        v_env_10494_,
        v___x_10495_,
        v___x_2152__boxed_10501_,
        v_e_10497_,
        v___y_10498_,
        v___y_10499_,
    );
    leanh::lean_dec(v___y_10499_);
    leanh::lean_dec_ref(v___y_10498_);
    return v_res_10502_;
}
pub unsafe fn l_Lean_Meta_unfoldDeclsFrom___lam__0(
    mut v_biggerEnv_10503_: *mut leanh::LeanObject,
    mut v_e_10504_: *mut leanh::LeanObject,
    mut v___f_10505_: *mut leanh::LeanObject,
    mut v___y_10506_: *mut leanh::LeanObject,
    mut v___y_10507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10510_: u8 = 0;
    let mut v___x_10511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_10513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_10515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10509_ = lean_st_ref_get(v___y_10507_);
    v___x_10510_ = 0;
    v___x_10511_ = l_Lean_Environment_setExporting(v_biggerEnv_10503_, v___x_10510_);
    leanh::lean_inc_ref(v___x_10511_);
    v___x_10512_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(
        v___x_10511_,
        v___y_10507_,
    );
    leanh::lean_dec_ref(v___x_10512_);
    v_env_10513_ = leanh::lean_ctor_get(v___x_10509_, 0);
    leanh::lean_inc_ref(v_env_10513_);
    leanh::lean_dec(v___x_10509_);
    v___x_10514_ = leanh::lean_box((v___x_10510_) as usize);
    v___f_10515_ = leanh::lean_alloc_closure(
        l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed as *mut core::ffi::c_void,
        7,
        3,
    );
    leanh::lean_closure_set(v___f_10515_, 0, v_env_10513_);
    leanh::lean_closure_set(v___f_10515_, 1, v___x_10511_);
    leanh::lean_closure_set(v___f_10515_, 2, v___x_10514_);
    v___x_10516_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(
        v_e_10504_,
        v___f_10515_,
        v___f_10505_,
        v___y_10506_,
        v___y_10507_,
    );
    return v___x_10516_;
}
pub unsafe fn l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed(
    mut v_biggerEnv_10517_: *mut leanh::LeanObject,
    mut v_e_10518_: *mut leanh::LeanObject,
    mut v___f_10519_: *mut leanh::LeanObject,
    mut v___y_10520_: *mut leanh::LeanObject,
    mut v___y_10521_: *mut leanh::LeanObject,
    mut v___y_10522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_10523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_10523_ = l_Lean_Meta_unfoldDeclsFrom___lam__0(
        v_biggerEnv_10517_,
        v_e_10518_,
        v___f_10519_,
        v___y_10520_,
        v___y_10521_,
    );
    leanh::lean_dec(v___y_10521_);
    leanh::lean_dec_ref(v___y_10520_);
    return v_res_10523_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(
    mut v_env_10524_: *mut leanh::LeanObject,
    mut v_x_10525_: *mut leanh::LeanObject,
    mut v___y_10526_: *mut leanh::LeanObject,
    mut v___y_10527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_10530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_10532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_10536_: u8 = 0;
    let mut v___x_10538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10540_: u8 = 0;
    let mut v_unused_10541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_10544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_10548_: u8 = 0;
    let mut v___x_10550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10552_: u8 = 0;
    let mut v_unused_10553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_10554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10529_ = lean_st_ref_get(v___y_10527_);
                v_env_10530_ = leanh::lean_ctor_get(v___x_10529_, 0);
                leanh::lean_inc_ref(v_env_10530_);
                leanh::lean_dec(v___x_10529_);
                v___x_10542_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(
                    v_env_10524_,
                    v___y_10527_,
                );
                leanh::lean_dec_ref(v___x_10542_);
                leanh::lean_inc(v___y_10527_);
                leanh::lean_inc_ref(v___y_10526_);
                v___x_10543_ = leanh::lean_apply_3(
                    v_x_10525_,
                    v___y_10526_,
                    v___y_10527_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_10543_) == 0 {
                    v_a_10544_ = leanh::lean_ctor_get(v___x_10543_, 0);
                    leanh::lean_inc(v_a_10544_);
                    leanh::lean_dec_ref_known(v___x_10543_, 1);
                    v___x_10545_ =
                        l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(
                            v_env_10530_,
                            v___y_10527_,
                        );
                    v_isSharedCheck_10552_ = (!leanh::lean_is_exclusive(v___x_10545_)) as u8;
                    if v_isSharedCheck_10552_ == 0 {
                        v_unused_10553_ = leanh::lean_ctor_get(v___x_10545_, 0);
                        leanh::lean_dec(v_unused_10553_);
                        v___x_10547_ = v___x_10545_;
                        v_isShared_10548_ = v_isSharedCheck_10552_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_10545_);
                        v___x_10547_ = leanh::lean_box(0);
                        v_isShared_10548_ = v_isSharedCheck_10552_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_10554_ = leanh::lean_ctor_get(v___x_10543_, 0);
                    leanh::lean_inc(v_a_10554_);
                    leanh::lean_dec_ref_known(v___x_10543_, 1);
                    v_a_10532_ = v_a_10554_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_10533_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(
                    v_env_10530_,
                    v___y_10527_,
                );
                v_isSharedCheck_10540_ = (!leanh::lean_is_exclusive(v___x_10533_)) as u8;
                if v_isSharedCheck_10540_ == 0 {
                    v_unused_10541_ = leanh::lean_ctor_get(v___x_10533_, 0);
                    leanh::lean_dec(v_unused_10541_);
                    v___x_10535_ = v___x_10533_;
                    v_isShared_10536_ = v_isSharedCheck_10540_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v___x_10533_);
                    v___x_10535_ = leanh::lean_box(0);
                    v_isShared_10536_ = v_isSharedCheck_10540_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_10536_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_10535_, 1);
                    leanh::lean_ctor_set(v___x_10535_, 0, v_a_10532_);
                    v___x_10538_ = v___x_10535_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_10539_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10539_, 0, v_a_10532_);
                    v___x_10538_ = v_reuseFailAlloc_10539_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_10538_;
            }
            4 => {
                if v_isShared_10548_ == 0 {
                    leanh::lean_ctor_set(v___x_10547_, 0, v_a_10544_);
                    v___x_10550_ = v___x_10547_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_10551_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10551_, 0, v_a_10544_);
                    v___x_10550_ = v_reuseFailAlloc_10551_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_10550_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg___boxed(
    mut v_env_10555_: *mut leanh::LeanObject,
    mut v_x_10556_: *mut leanh::LeanObject,
    mut v___y_10557_: *mut leanh::LeanObject,
    mut v___y_10558_: *mut leanh::LeanObject,
    mut v___y_10559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_10560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_10560_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(
        v_env_10555_,
        v_x_10556_,
        v___y_10557_,
        v___y_10558_,
    );
    leanh::lean_dec(v___y_10558_);
    leanh::lean_dec_ref(v___y_10557_);
    return v_res_10560_;
}
pub unsafe fn l_Lean_Meta_unfoldDeclsFrom(
    mut v_biggerEnv_10561_: *mut leanh::LeanObject,
    mut v_e_10562_: *mut leanh::LeanObject,
    mut v_a_10563_: *mut leanh::LeanObject,
    mut v_a_10564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_10567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_10568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_10569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10566_ = lean_st_ref_get(v_a_10564_);
    v_env_10567_ = leanh::lean_ctor_get(v___x_10566_, 0);
    leanh::lean_inc_ref(v_env_10567_);
    leanh::lean_dec(v___x_10566_);
    v___f_10568_ = l_Lean_Core_betaReduce___closed__1;
    v___f_10569_ = leanh::lean_alloc_closure(
        l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_10569_, 0, v_biggerEnv_10561_);
    leanh::lean_closure_set(v___f_10569_, 1, v_e_10562_);
    leanh::lean_closure_set(v___f_10569_, 2, v___f_10568_);
    v___x_10570_ = l_Lean_Environment_unlockAsync(v_env_10567_);
    v___x_10571_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(
        v___x_10570_,
        v___f_10569_,
        v_a_10563_,
        v_a_10564_,
    );
    return v___x_10571_;
}
pub unsafe fn l_Lean_Meta_unfoldDeclsFrom___boxed(
    mut v_biggerEnv_10572_: *mut leanh::LeanObject,
    mut v_e_10573_: *mut leanh::LeanObject,
    mut v_a_10574_: *mut leanh::LeanObject,
    mut v_a_10575_: *mut leanh::LeanObject,
    mut v_a_10576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_10577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_10577_ =
        l_Lean_Meta_unfoldDeclsFrom(v_biggerEnv_10572_, v_e_10573_, v_a_10574_, v_a_10575_);
    leanh::lean_dec(v_a_10575_);
    leanh::lean_dec_ref(v_a_10574_);
    return v_res_10577_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(
    mut v_00_u03b1_10578_: *mut leanh::LeanObject,
    mut v_env_10579_: *mut leanh::LeanObject,
    mut v_x_10580_: *mut leanh::LeanObject,
    mut v___y_10581_: *mut leanh::LeanObject,
    mut v___y_10582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10584_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(
        v_env_10579_,
        v_x_10580_,
        v___y_10581_,
        v___y_10582_,
    );
    return v___x_10584_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___boxed(
    mut v_00_u03b1_10585_: *mut leanh::LeanObject,
    mut v_env_10586_: *mut leanh::LeanObject,
    mut v_x_10587_: *mut leanh::LeanObject,
    mut v___y_10588_: *mut leanh::LeanObject,
    mut v___y_10589_: *mut leanh::LeanObject,
    mut v___y_10590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_10591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_10591_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(
        v_00_u03b1_10585_,
        v_env_10586_,
        v_x_10587_,
        v___y_10588_,
        v___y_10589_,
    );
    leanh::lean_dec(v___y_10589_);
    leanh::lean_dec_ref(v___y_10588_);
    return v_res_10591_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(
    mut v_af_10592_: *mut leanh::LeanObject,
    mut v_axs_10593_: *mut leanh::LeanObject,
    mut v_numSectionVars_10594_: *mut leanh::LeanObject,
    mut v_as_10595_: *mut leanh::LeanObject,
    mut v_i_10596_: usize,
    mut v_stop_10597_: usize,
) -> u8 {
    let mut v___x_10598_: u8 = 0;
    let mut v___x_10599_: u8 = 0;
    let mut v___y_10601_: u8 = 0;
    let mut v___x_10602_: usize = 0;
    let mut v___x_10603_: usize = 0;
    let mut v___x_10605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10607_: u8 = 0;
    let mut v___x_10608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10609_: u8 = 0;
    let mut v___x_10610_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10598_ = lean_usize_dec_eq(v_i_10596_, v_stop_10597_);
                if v___x_10598_ == 0 {
                    v___x_10599_ = 1;
                    v___x_10605_ = lean_array_uget_borrowed(v_as_10595_, v_i_10596_);
                    v___x_10606_ = l_Lean_Expr_constName_x21(v_af_10592_);
                    v___x_10607_ = lean_name_eq(v___x_10606_, v___x_10605_);
                    leanh::lean_dec(v___x_10606_);
                    if v___x_10607_ == 0 {
                        v___y_10601_ = v___x_10607_;
                        state = 1;
                        continue;
                    } else {
                        v___x_10608_ = lean_array_get_size(v_axs_10593_);
                        v___x_10609_ = lean_nat_dec_le(v___x_10608_, v_numSectionVars_10594_);
                        v___y_10601_ = v___x_10609_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_10610_ = 0;
                    return v___x_10610_;
                }
            }
            1 => {
                if v___y_10601_ == 0 {
                    v___x_10602_ = 1usize;
                    v___x_10603_ = lean_usize_add(v_i_10596_, v___x_10602_);
                    v_i_10596_ = v___x_10603_;
                    state = 0;
                    continue;
                } else {
                    return v___x_10599_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0___boxed(
    mut v_af_10611_: *mut leanh::LeanObject,
    mut v_axs_10612_: *mut leanh::LeanObject,
    mut v_numSectionVars_10613_: *mut leanh::LeanObject,
    mut v_as_10614_: *mut leanh::LeanObject,
    mut v_i_10615_: *mut leanh::LeanObject,
    mut v_stop_10616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_10617_: usize = 0;
    let mut v_stop_boxed_10618_: usize = 0;
    let mut v_res_10619_: u8 = 0;
    let mut v_r_10620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_10617_ = leanh::lean_unbox_usize(v_i_10615_);
    leanh::lean_dec(v_i_10615_);
    v_stop_boxed_10618_ = leanh::lean_unbox_usize(v_stop_10616_);
    leanh::lean_dec(v_stop_10616_);
    v_res_10619_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_af_10611_, v_axs_10612_, v_numSectionVars_10613_, v_as_10614_, v_i_boxed_10617_, v_stop_boxed_10618_);
    leanh::lean_dec_ref(v_as_10614_);
    leanh::lean_dec(v_numSectionVars_10613_);
    leanh::lean_dec_ref(v_axs_10612_);
    leanh::lean_dec_ref(v_af_10611_);
    v_r_10620_ = leanh::lean_box((v_res_10619_) as usize);
    return v_r_10620_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(
    mut v_fnNames_10621_: *mut leanh::LeanObject,
    mut v_numSectionVars_10622_: *mut leanh::LeanObject,
    mut v_x_10623_: *mut leanh::LeanObject,
    mut v_x_10624_: *mut leanh::LeanObject,
    mut v_x_10625_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_fn_10626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_10627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10632_: u8 = 0;
    let mut v___x_10633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10635_: u8 = 0;
    let mut v___x_10636_: usize = 0;
    let mut v___x_10637_: usize = 0;
    let mut v___x_10638_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_10623_) == 5 {
                    v_fn_10626_ = leanh::lean_ctor_get(v_x_10623_, 0);
                    leanh::lean_inc_ref(v_fn_10626_);
                    v_arg_10627_ = leanh::lean_ctor_get(v_x_10623_, 1);
                    leanh::lean_inc_ref(v_arg_10627_);
                    leanh::lean_dec_ref_known(v_x_10623_, 2);
                    v___x_10628_ = lean_array_set(v_x_10624_, v_x_10625_, v_arg_10627_);
                    v___x_10629_ = leanh::lean_unsigned_to_nat(1);
                    v___x_10630_ = lean_nat_sub(v_x_10625_, v___x_10629_);
                    leanh::lean_dec(v_x_10625_);
                    v_x_10623_ = v_fn_10626_;
                    v_x_10624_ = v___x_10628_;
                    v_x_10625_ = v___x_10630_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_x_10625_);
                    v___x_10632_ = l_Lean_Expr_isConst(v_x_10623_);
                    if v___x_10632_ == 0 {
                        leanh::lean_dec_ref(v_x_10624_);
                        leanh::lean_dec_ref(v_x_10623_);
                        return v___x_10632_;
                    } else {
                        v___x_10633_ = leanh::lean_unsigned_to_nat(0);
                        v___x_10634_ = lean_array_get_size(v_fnNames_10621_);
                        v___x_10635_ = lean_nat_dec_lt(v___x_10633_, v___x_10634_);
                        if v___x_10635_ == 0 {
                            leanh::lean_dec_ref(v_x_10624_);
                            leanh::lean_dec_ref(v_x_10623_);
                            return v___x_10635_;
                        } else {
                            if v___x_10635_ == 0 {
                                leanh::lean_dec_ref(v_x_10624_);
                                leanh::lean_dec_ref(v_x_10623_);
                                return v___x_10635_;
                            } else {
                                v___x_10636_ = 0usize;
                                v___x_10637_ = lean_usize_of_nat(v___x_10634_);
                                v___x_10638_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_10623_, v_x_10624_, v_numSectionVars_10622_, v_fnNames_10621_, v___x_10636_, v___x_10637_);
                                leanh::lean_dec_ref(v_x_10624_);
                                leanh::lean_dec_ref(v_x_10623_);
                                return v___x_10638_;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1___boxed(
    mut v_fnNames_10639_: *mut leanh::LeanObject,
    mut v_numSectionVars_10640_: *mut leanh::LeanObject,
    mut v_x_10641_: *mut leanh::LeanObject,
    mut v_x_10642_: *mut leanh::LeanObject,
    mut v_x_10643_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_10644_: u8 = 0;
    let mut v_r_10645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_10644_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_10639_, v_numSectionVars_10640_, v_x_10641_, v_x_10642_, v_x_10643_);
    leanh::lean_dec(v_numSectionVars_10640_);
    leanh::lean_dec_ref(v_fnNames_10639_);
    v_r_10645_ = leanh::lean_box((v_res_10644_) as usize);
    return v_r_10645_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(
    mut v_numSectionVars_10646_: *mut leanh::LeanObject,
    mut v_fnNames_10647_: *mut leanh::LeanObject,
    mut v_x_10648_: *mut leanh::LeanObject,
    mut v_x_10649_: *mut leanh::LeanObject,
    mut v_x_10650_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_10648_) == 5 {
        let mut v_fn_10651_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_arg_10652_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_10653_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_10654_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_10655_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_10656_: u8 = 0;
        v_fn_10651_ = leanh::lean_ctor_get(v_x_10648_, 0);
        leanh::lean_inc_ref(v_fn_10651_);
        v_arg_10652_ = leanh::lean_ctor_get(v_x_10648_, 1);
        leanh::lean_inc_ref(v_arg_10652_);
        leanh::lean_dec_ref_known(v_x_10648_, 2);
        v___x_10653_ = lean_array_set(v_x_10649_, v_x_10650_, v_arg_10652_);
        v___x_10654_ = leanh::lean_unsigned_to_nat(1);
        v___x_10655_ = lean_nat_sub(v_x_10650_, v___x_10654_);
        v___x_10656_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_10647_, v_numSectionVars_10646_, v_fn_10651_, v___x_10653_, v___x_10655_);
        return v___x_10656_;
    } else {
        let mut v___x_10657_: u8 = 0;
        v___x_10657_ = l_Lean_Expr_isConst(v_x_10648_);
        if v___x_10657_ == 0 {
            leanh::lean_dec_ref(v_x_10649_);
            leanh::lean_dec_ref(v_x_10648_);
            return v___x_10657_;
        } else {
            let mut v___x_10658_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_10659_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_10660_: u8 = 0;
            v___x_10658_ = leanh::lean_unsigned_to_nat(0);
            v___x_10659_ = lean_array_get_size(v_fnNames_10647_);
            v___x_10660_ = lean_nat_dec_lt(v___x_10658_, v___x_10659_);
            if v___x_10660_ == 0 {
                leanh::lean_dec_ref(v_x_10649_);
                leanh::lean_dec_ref(v_x_10648_);
                return v___x_10660_;
            } else {
                if v___x_10660_ == 0 {
                    leanh::lean_dec_ref(v_x_10649_);
                    leanh::lean_dec_ref(v_x_10648_);
                    return v___x_10660_;
                } else {
                    let mut v___x_10661_: usize = 0;
                    let mut v___x_10662_: usize = 0;
                    let mut v___x_10663_: u8 = 0;
                    v___x_10661_ = 0usize;
                    v___x_10662_ = lean_usize_of_nat(v___x_10659_);
                    v___x_10663_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_10648_, v_x_10649_, v_numSectionVars_10646_, v_fnNames_10647_, v___x_10661_, v___x_10662_);
                    leanh::lean_dec_ref(v_x_10649_);
                    leanh::lean_dec_ref(v_x_10648_);
                    return v___x_10663_;
                }
            }
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1___boxed(
    mut v_numSectionVars_10664_: *mut leanh::LeanObject,
    mut v_fnNames_10665_: *mut leanh::LeanObject,
    mut v_x_10666_: *mut leanh::LeanObject,
    mut v_x_10667_: *mut leanh::LeanObject,
    mut v_x_10668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_10669_: u8 = 0;
    let mut v_r_10670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_10669_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_10664_, v_fnNames_10665_, v_x_10666_, v_x_10667_, v_x_10668_);
    leanh::lean_dec(v_x_10668_);
    leanh::lean_dec_ref(v_fnNames_10665_);
    leanh::lean_dec(v_numSectionVars_10664_);
    v_r_10670_ = leanh::lean_box((v_res_10669_) as usize);
    return v_r_10670_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(
    mut v_fnNames_10671_: *mut leanh::LeanObject,
    mut v_numSectionVars_10672_: *mut leanh::LeanObject,
    mut v_a_10673_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_dummy_10674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_10675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10679_: u8 = 0;
    v_dummy_10674_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once), _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
    v_nargs_10675_ = l_Lean_Expr_getAppNumArgs(v_a_10673_);
    leanh::lean_inc(v_nargs_10675_);
    v___x_10676_ = lean_mk_array(v_nargs_10675_, v_dummy_10674_);
    v___x_10677_ = leanh::lean_unsigned_to_nat(1);
    v___x_10678_ = lean_nat_sub(v_nargs_10675_, v___x_10677_);
    leanh::lean_dec(v_nargs_10675_);
    v___x_10679_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_10672_, v_fnNames_10671_, v_a_10673_, v___x_10676_, v___x_10678_);
    leanh::lean_dec(v___x_10678_);
    return v___x_10679_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg___boxed(
    mut v_fnNames_10680_: *mut leanh::LeanObject,
    mut v_numSectionVars_10681_: *mut leanh::LeanObject,
    mut v_a_10682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_10683_: u8 = 0;
    let mut v_r_10684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_10683_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(
        v_fnNames_10680_,
        v_numSectionVars_10681_,
        v_a_10682_,
    );
    leanh::lean_dec(v_numSectionVars_10681_);
    leanh::lean_dec_ref(v_fnNames_10680_);
    v_r_10684_ = leanh::lean_box((v_res_10683_) as usize);
    return v_r_10684_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(
    mut v_fnNames_10685_: *mut leanh::LeanObject,
    mut v_numSectionVars_10686_: *mut leanh::LeanObject,
    mut v_as_10687_: *mut leanh::LeanObject,
    mut v_i_10688_: usize,
    mut v_stop_10689_: usize,
) -> u8 {
    let mut v___x_10690_: u8 = 0;
    let mut v___x_10691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10692_: u8 = 0;
    let mut v___x_10693_: usize = 0;
    let mut v___x_10694_: usize = 0;
    let mut v___x_10696_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10690_ = lean_usize_dec_eq(v_i_10688_, v_stop_10689_);
                if v___x_10690_ == 0 {
                    v___x_10691_ = lean_array_uget_borrowed(v_as_10687_, v_i_10688_);
                    leanh::lean_inc(v___x_10691_);
                    v___x_10692_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_10685_, v_numSectionVars_10686_, v___x_10691_);
                    if v___x_10692_ == 0 {
                        v___x_10693_ = 1usize;
                        v___x_10694_ = lean_usize_add(v_i_10688_, v___x_10693_);
                        v_i_10688_ = v___x_10694_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_10692_;
                    }
                } else {
                    v___x_10696_ = 0;
                    return v___x_10696_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0___boxed(
    mut v_fnNames_10697_: *mut leanh::LeanObject,
    mut v_numSectionVars_10698_: *mut leanh::LeanObject,
    mut v_as_10699_: *mut leanh::LeanObject,
    mut v_i_10700_: *mut leanh::LeanObject,
    mut v_stop_10701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_10702_: usize = 0;
    let mut v_stop_boxed_10703_: usize = 0;
    let mut v_res_10704_: u8 = 0;
    let mut v_r_10705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_10702_ = leanh::lean_unbox_usize(v_i_10700_);
    leanh::lean_dec(v_i_10700_);
    v_stop_boxed_10703_ = leanh::lean_unbox_usize(v_stop_10701_);
    leanh::lean_dec(v_stop_10701_);
    v_res_10704_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_10697_, v_numSectionVars_10698_, v_as_10699_, v_i_boxed_10702_, v_stop_boxed_10703_);
    leanh::lean_dec_ref(v_as_10699_);
    leanh::lean_dec(v_numSectionVars_10698_);
    leanh::lean_dec_ref(v_fnNames_10697_);
    v_r_10705_ = leanh::lean_box((v_res_10704_) as usize);
    return v_r_10705_;
}
pub unsafe fn l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(
    mut v_fnNames_10706_: *mut leanh::LeanObject,
    mut v_numSectionVars_10707_: *mut leanh::LeanObject,
    mut v___x_10708_: *mut leanh::LeanObject,
    mut v_x_10709_: *mut leanh::LeanObject,
    mut v_x_10710_: *mut leanh::LeanObject,
    mut v___y_10711_: *mut leanh::LeanObject,
    mut v___y_10712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_10717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_10718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10721_: u8 = 0;
    let mut v___x_10722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10724_: u8 = 0;
    let mut v___x_10725_: usize = 0;
    let mut v___x_10726_: usize = 0;
    let mut v___x_10727_: u8 = 0;
    let mut v___x_10728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10729_: u8 = 0;
    let mut v___x_10730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_10731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_10736_: u8 = 0;
    let mut v_a_10737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_10740_: u8 = 0;
    let mut v___x_10741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10748_: u8 = 0;
    let mut v_a_10749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_10752_: u8 = 0;
    let mut v___x_10754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10756_: u8 = 0;
    let mut v_isSharedCheck_10757_: u8 = 0;
    let mut v_unused_10758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_10709_) == 5 {
                    v_fn_10717_ = leanh::lean_ctor_get(v_x_10709_, 0);
                    leanh::lean_inc_ref(v_fn_10717_);
                    v_arg_10718_ = leanh::lean_ctor_get(v_x_10709_, 1);
                    leanh::lean_inc_ref(v_arg_10718_);
                    leanh::lean_dec_ref_known(v_x_10709_, 2);
                    v___x_10719_ = lean_array_push(v_x_10710_, v_arg_10718_);
                    v_x_10709_ = v_fn_10717_;
                    v_x_10710_ = v___x_10719_;
                    state = 0;
                    continue;
                } else {
                    v___x_10721_ = l_Lean_Expr_isConst(v_x_10709_);
                    if v___x_10721_ == 0 {
                        leanh::lean_dec_ref(v_x_10710_);
                        leanh::lean_dec_ref(v_x_10709_);
                        leanh::lean_dec_ref(v___x_10708_);
                        state = 1;
                        continue;
                    } else {
                        v___x_10722_ = leanh::lean_unsigned_to_nat(0);
                        v___x_10723_ = lean_array_get_size(v_x_10710_);
                        v___x_10724_ = lean_nat_dec_lt(v___x_10722_, v___x_10723_);
                        if v___x_10724_ == 0 {
                            leanh::lean_dec_ref(v_x_10710_);
                            leanh::lean_dec_ref(v_x_10709_);
                            leanh::lean_dec_ref(v___x_10708_);
                            state = 1;
                            continue;
                        } else {
                            if v___x_10724_ == 0 {
                                leanh::lean_dec_ref(v_x_10710_);
                                leanh::lean_dec_ref(v_x_10709_);
                                leanh::lean_dec_ref(v___x_10708_);
                                state = 1;
                                continue;
                            } else {
                                v___x_10725_ = 0usize;
                                v___x_10726_ = lean_usize_of_nat(v___x_10723_);
                                v___x_10727_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_10706_, v_numSectionVars_10707_, v_x_10710_, v___x_10725_, v___x_10726_);
                                if v___x_10727_ == 0 {
                                    leanh::lean_dec_ref(v_x_10710_);
                                    leanh::lean_dec_ref(v_x_10709_);
                                    leanh::lean_dec_ref(v___x_10708_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_10728_ = l_Lean_Expr_constName_x21(v_x_10709_);
                                    v___x_10729_ = 0;
                                    v___x_10730_ = l_Lean_Environment_find_x3f(
                                        v___x_10708_,
                                        v___x_10728_,
                                        v___x_10729_,
                                    );
                                    if leanh::lean_obj_tag(v___x_10730_) == 1 {
                                        v_val_10731_ = leanh::lean_ctor_get(v___x_10730_, 0);
                                        leanh::lean_inc(v_val_10731_);
                                        leanh::lean_dec_ref_known(v___x_10730_, 1);
                                        if leanh::lean_obj_tag(v_val_10731_) == 2 {
                                            v___x_10732_ = l_Lean_Expr_constLevels_x21(v_x_10709_);
                                            leanh::lean_dec_ref(v_x_10709_);
                                            v___x_10733_ = l_Lean_Core_instantiateValueLevelParams(
                                                v_val_10731_,
                                                v___x_10732_,
                                                v___x_10721_,
                                                v___y_10711_,
                                                v___y_10712_,
                                            );
                                            v_isSharedCheck_10757_ =
                                                (!leanh::lean_is_exclusive(v_val_10731_))
                                                    as u8;
                                            if v_isSharedCheck_10757_ == 0 {
                                                v_unused_10758_ =
                                                    leanh::lean_ctor_get(v_val_10731_, 0);
                                                leanh::lean_dec(v_unused_10758_);
                                                v___x_10735_ = v_val_10731_;
                                                v_isShared_10736_ = v_isSharedCheck_10757_;
                                                state = 2;
                                                continue;
                                            } else {
                                                leanh::lean_dec(v_val_10731_);
                                                v___x_10735_ = leanh::lean_box(0);
                                                v_isShared_10736_ = v_isSharedCheck_10757_;
                                                state = 2;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec(v_val_10731_);
                                            leanh::lean_dec_ref(v_x_10710_);
                                            leanh::lean_dec_ref(v_x_10709_);
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v___x_10730_);
                                        leanh::lean_dec_ref(v_x_10710_);
                                        leanh::lean_dec_ref(v_x_10709_);
                                        state = 1;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_10715_ = l_Lean_Core_betaReduce___lam__0___closed__0;
                v___x_10716_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_10716_, 0, v___x_10715_);
                return v___x_10716_;
            }
            2 => {
                if leanh::lean_obj_tag(v___x_10733_) == 0 {
                    v_a_10737_ = leanh::lean_ctor_get(v___x_10733_, 0);
                    v_isSharedCheck_10748_ = (!leanh::lean_is_exclusive(v___x_10733_)) as u8;
                    if v_isSharedCheck_10748_ == 0 {
                        v___x_10739_ = v___x_10733_;
                        v_isShared_10740_ = v_isSharedCheck_10748_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_10737_);
                        leanh::lean_dec(v___x_10733_);
                        v___x_10739_ = leanh::lean_box(0);
                        v_isShared_10740_ = v_isSharedCheck_10748_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_10735_);
                    leanh::lean_dec_ref(v_x_10710_);
                    v_a_10749_ = leanh::lean_ctor_get(v___x_10733_, 0);
                    v_isSharedCheck_10756_ = (!leanh::lean_is_exclusive(v___x_10733_)) as u8;
                    if v_isSharedCheck_10756_ == 0 {
                        v___x_10751_ = v___x_10733_;
                        v_isShared_10752_ = v_isSharedCheck_10756_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_10749_);
                        leanh::lean_dec(v___x_10733_);
                        v___x_10751_ = leanh::lean_box(0);
                        v_isShared_10752_ = v_isSharedCheck_10756_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_10741_ =
                    l_Lean_Expr_betaRev(v_a_10737_, v_x_10710_, v___x_10729_, v___x_10729_);
                leanh::lean_dec_ref(v_x_10710_);
                if v_isShared_10736_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_10735_, 1);
                    leanh::lean_ctor_set(v___x_10735_, 0, v___x_10741_);
                    v___x_10743_ = v___x_10735_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_10747_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10747_, 0, v___x_10741_);
                    v___x_10743_ = v_reuseFailAlloc_10747_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_10740_ == 0 {
                    leanh::lean_ctor_set(v___x_10739_, 0, v___x_10743_);
                    v___x_10745_ = v___x_10739_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_10746_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10746_, 0, v___x_10743_);
                    v___x_10745_ = v_reuseFailAlloc_10746_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_10745_;
            }
            6 => {
                if v_isShared_10752_ == 0 {
                    v___x_10754_ = v___x_10751_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_10755_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10755_, 0, v_a_10749_);
                    v___x_10754_ = v_reuseFailAlloc_10755_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_10754_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1___boxed(
    mut v_fnNames_10759_: *mut leanh::LeanObject,
    mut v_numSectionVars_10760_: *mut leanh::LeanObject,
    mut v___x_10761_: *mut leanh::LeanObject,
    mut v_x_10762_: *mut leanh::LeanObject,
    mut v_x_10763_: *mut leanh::LeanObject,
    mut v___y_10764_: *mut leanh::LeanObject,
    mut v___y_10765_: *mut leanh::LeanObject,
    mut v___y_10766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_10767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_10767_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_10759_, v_numSectionVars_10760_, v___x_10761_, v_x_10762_, v_x_10763_, v___y_10764_, v___y_10765_);
    leanh::lean_dec(v___y_10765_);
    leanh::lean_dec_ref(v___y_10764_);
    leanh::lean_dec(v_numSectionVars_10760_);
    leanh::lean_dec_ref(v_fnNames_10759_);
    return v_res_10767_;
}
pub unsafe fn l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(
    mut v_fnNames_10768_: *mut leanh::LeanObject,
    mut v_numSectionVars_10769_: *mut leanh::LeanObject,
    mut v_env_10770_: *mut leanh::LeanObject,
    mut v_e_10771_: *mut leanh::LeanObject,
    mut v___y_10772_: *mut leanh::LeanObject,
    mut v___y_10773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10775_ = l_Lean_Expr_getAppNumArgs(v_e_10771_);
    v___x_10776_ = lean_mk_empty_array_with_capacity(v___x_10775_);
    leanh::lean_dec(v___x_10775_);
    v___x_10777_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_10768_, v_numSectionVars_10769_, v_env_10770_, v_e_10771_, v___x_10776_, v___y_10772_, v___y_10773_);
    return v___x_10777_;
}
pub unsafe fn l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed(
    mut v_fnNames_10778_: *mut leanh::LeanObject,
    mut v_numSectionVars_10779_: *mut leanh::LeanObject,
    mut v_env_10780_: *mut leanh::LeanObject,
    mut v_e_10781_: *mut leanh::LeanObject,
    mut v___y_10782_: *mut leanh::LeanObject,
    mut v___y_10783_: *mut leanh::LeanObject,
    mut v___y_10784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_10785_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_10785_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(
        v_fnNames_10778_,
        v_numSectionVars_10779_,
        v_env_10780_,
        v_e_10781_,
        v___y_10782_,
        v___y_10783_,
    );
    leanh::lean_dec(v___y_10783_);
    leanh::lean_dec_ref(v___y_10782_);
    leanh::lean_dec(v_numSectionVars_10779_);
    leanh::lean_dec_ref(v_fnNames_10778_);
    return v_res_10785_;
}
pub unsafe fn l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(
    mut v_fnNames_10786_: *mut leanh::LeanObject,
    mut v_numSectionVars_10787_: *mut leanh::LeanObject,
    mut v_e_10788_: *mut leanh::LeanObject,
    mut v___f_10789_: *mut leanh::LeanObject,
    mut v___y_10790_: *mut leanh::LeanObject,
    mut v___y_10791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_10794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_10795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10793_ = lean_st_ref_get(v___y_10791_);
    v_env_10794_ = leanh::lean_ctor_get(v___x_10793_, 0);
    leanh::lean_inc_ref(v_env_10794_);
    leanh::lean_dec(v___x_10793_);
    v___f_10795_ = leanh::lean_alloc_closure(
        l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed as *mut core::ffi::c_void,
        7,
        3,
    );
    leanh::lean_closure_set(v___f_10795_, 0, v_fnNames_10786_);
    leanh::lean_closure_set(v___f_10795_, 1, v_numSectionVars_10787_);
    leanh::lean_closure_set(v___f_10795_, 2, v_env_10794_);
    v___x_10796_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(
        v_e_10788_,
        v___f_10795_,
        v___f_10789_,
        v___y_10790_,
        v___y_10791_,
    );
    return v___x_10796_;
}
pub unsafe fn l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed(
    mut v_fnNames_10797_: *mut leanh::LeanObject,
    mut v_numSectionVars_10798_: *mut leanh::LeanObject,
    mut v_e_10799_: *mut leanh::LeanObject,
    mut v___f_10800_: *mut leanh::LeanObject,
    mut v___y_10801_: *mut leanh::LeanObject,
    mut v___y_10802_: *mut leanh::LeanObject,
    mut v___y_10803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_10804_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_10804_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(
        v_fnNames_10797_,
        v_numSectionVars_10798_,
        v_e_10799_,
        v___f_10800_,
        v___y_10801_,
        v___y_10802_,
    );
    leanh::lean_dec(v___y_10802_);
    leanh::lean_dec_ref(v___y_10801_);
    return v_res_10804_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(
    mut v___y_10805_: *mut leanh::LeanObject,
    mut v_isExporting_10806_: u8,
    mut v___x_10807_: *mut leanh::LeanObject,
    mut v_a_x3f_10808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_10811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_10812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_10813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_10814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_10815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_10816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_10817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_10818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_10821_: u8 = 0;
    let mut v___x_10822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10829_: u8 = 0;
    let mut v_unused_10830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10810_ = lean_st_ref_take(v___y_10805_);
                v_env_10811_ = leanh::lean_ctor_get(v___x_10810_, 0);
                v_nextMacroScope_10812_ = leanh::lean_ctor_get(v___x_10810_, 1);
                v_ngen_10813_ = leanh::lean_ctor_get(v___x_10810_, 2);
                v_auxDeclNGen_10814_ = leanh::lean_ctor_get(v___x_10810_, 3);
                v_traceState_10815_ = leanh::lean_ctor_get(v___x_10810_, 4);
                v_messages_10816_ = leanh::lean_ctor_get(v___x_10810_, 6);
                v_infoState_10817_ = leanh::lean_ctor_get(v___x_10810_, 7);
                v_snapshotTasks_10818_ = leanh::lean_ctor_get(v___x_10810_, 8);
                v_isSharedCheck_10829_ = (!leanh::lean_is_exclusive(v___x_10810_)) as u8;
                if v_isSharedCheck_10829_ == 0 {
                    v_unused_10830_ = leanh::lean_ctor_get(v___x_10810_, 5);
                    leanh::lean_dec(v_unused_10830_);
                    v___x_10820_ = v___x_10810_;
                    v_isShared_10821_ = v_isSharedCheck_10829_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_10818_);
                    leanh::lean_inc(v_infoState_10817_);
                    leanh::lean_inc(v_messages_10816_);
                    leanh::lean_inc(v_traceState_10815_);
                    leanh::lean_inc(v_auxDeclNGen_10814_);
                    leanh::lean_inc(v_ngen_10813_);
                    leanh::lean_inc(v_nextMacroScope_10812_);
                    leanh::lean_inc(v_env_10811_);
                    leanh::lean_dec(v___x_10810_);
                    v___x_10820_ = leanh::lean_box(0);
                    v_isShared_10821_ = v_isSharedCheck_10829_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_10822_ = l_Lean_Environment_setExporting(v_env_10811_, v_isExporting_10806_);
                if v_isShared_10821_ == 0 {
                    leanh::lean_ctor_set(v___x_10820_, 5, v___x_10807_);
                    leanh::lean_ctor_set(v___x_10820_, 0, v___x_10822_);
                    v___x_10824_ = v___x_10820_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10828_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10828_, 0, v___x_10822_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_10828_,
                        1,
                        v_nextMacroScope_10812_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_10828_, 2, v_ngen_10813_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10828_, 3, v_auxDeclNGen_10814_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10828_, 4, v_traceState_10815_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10828_, 5, v___x_10807_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10828_, 6, v_messages_10816_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10828_, 7, v_infoState_10817_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10828_, 8, v_snapshotTasks_10818_);
                    v___x_10824_ = v_reuseFailAlloc_10828_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_10825_ = lean_st_ref_set(v___y_10805_, v___x_10824_);
                v___x_10826_ = leanh::lean_box(0);
                v___x_10827_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_10827_, 0, v___x_10826_);
                return v___x_10827_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0___boxed(
    mut v___y_10831_: *mut leanh::LeanObject,
    mut v_isExporting_10832_: *mut leanh::LeanObject,
    mut v___x_10833_: *mut leanh::LeanObject,
    mut v_a_x3f_10834_: *mut leanh::LeanObject,
    mut v___y_10835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_10836_: u8 = 0;
    let mut v_res_10837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_10836_ = (leanh::lean_unbox(v_isExporting_10832_) as u8);
    v_res_10837_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_10831_, v_isExporting_boxed_10836_, v___x_10833_, v_a_x3f_10834_);
    leanh::lean_dec(v_a_x3f_10834_);
    leanh::lean_dec(v___y_10831_);
    return v_res_10837_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(
    mut v_x_10838_: *mut leanh::LeanObject,
    mut v_isExporting_10839_: u8,
    mut v___y_10840_: *mut leanh::LeanObject,
    mut v___y_10841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_10844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_10845_: u8 = 0;
    let mut v___x_10846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_10847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_10848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_10849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_10850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_10851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_10852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_10853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_10854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_10857_: u8 = 0;
    let mut v___x_10858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_10863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_10864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_10867_: u8 = 0;
    let mut v___x_10869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_10873_: u8 = 0;
    let mut v___x_10875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10877_: u8 = 0;
    let mut v_unused_10878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10880_: u8 = 0;
    let mut v_a_10881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_10886_: u8 = 0;
    let mut v___x_10888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10890_: u8 = 0;
    let mut v_unused_10891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10893_: u8 = 0;
    let mut v_unused_10894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10843_ = lean_st_ref_get(v___y_10841_);
                v_env_10844_ = leanh::lean_ctor_get(v___x_10843_, 0);
                leanh::lean_inc_ref(v_env_10844_);
                leanh::lean_dec(v___x_10843_);
                v_isExporting_10845_ = leanh::lean_ctor_get_uint8(
                    v_env_10844_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                leanh::lean_dec_ref(v_env_10844_);
                v___x_10846_ = lean_st_ref_take(v___y_10841_);
                v_env_10847_ = leanh::lean_ctor_get(v___x_10846_, 0);
                v_nextMacroScope_10848_ = leanh::lean_ctor_get(v___x_10846_, 1);
                v_ngen_10849_ = leanh::lean_ctor_get(v___x_10846_, 2);
                v_auxDeclNGen_10850_ = leanh::lean_ctor_get(v___x_10846_, 3);
                v_traceState_10851_ = leanh::lean_ctor_get(v___x_10846_, 4);
                v_messages_10852_ = leanh::lean_ctor_get(v___x_10846_, 6);
                v_infoState_10853_ = leanh::lean_ctor_get(v___x_10846_, 7);
                v_snapshotTasks_10854_ = leanh::lean_ctor_get(v___x_10846_, 8);
                v_isSharedCheck_10893_ = (!leanh::lean_is_exclusive(v___x_10846_)) as u8;
                if v_isSharedCheck_10893_ == 0 {
                    v_unused_10894_ = leanh::lean_ctor_get(v___x_10846_, 5);
                    leanh::lean_dec(v_unused_10894_);
                    v___x_10856_ = v___x_10846_;
                    v_isShared_10857_ = v_isSharedCheck_10893_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_10854_);
                    leanh::lean_inc(v_infoState_10853_);
                    leanh::lean_inc(v_messages_10852_);
                    leanh::lean_inc(v_traceState_10851_);
                    leanh::lean_inc(v_auxDeclNGen_10850_);
                    leanh::lean_inc(v_ngen_10849_);
                    leanh::lean_inc(v_nextMacroScope_10848_);
                    leanh::lean_inc(v_env_10847_);
                    leanh::lean_dec(v___x_10846_);
                    v___x_10856_ = leanh::lean_box(0);
                    v_isShared_10857_ = v_isSharedCheck_10893_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_10858_ = l_Lean_Environment_setExporting(v_env_10847_, v_isExporting_10839_);
                v___x_10859_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once), _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
                if v_isShared_10857_ == 0 {
                    leanh::lean_ctor_set(v___x_10856_, 5, v___x_10859_);
                    leanh::lean_ctor_set(v___x_10856_, 0, v___x_10858_);
                    v___x_10861_ = v___x_10856_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10892_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10892_, 0, v___x_10858_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_10892_,
                        1,
                        v_nextMacroScope_10848_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_10892_, 2, v_ngen_10849_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10892_, 3, v_auxDeclNGen_10850_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10892_, 4, v_traceState_10851_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10892_, 5, v___x_10859_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10892_, 6, v_messages_10852_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10892_, 7, v_infoState_10853_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10892_, 8, v_snapshotTasks_10854_);
                    v___x_10861_ = v_reuseFailAlloc_10892_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_10862_ = lean_st_ref_set(v___y_10841_, v___x_10861_);
                leanh::lean_inc(v___y_10841_);
                leanh::lean_inc_ref(v___y_10840_);
                v_r_10863_ = leanh::lean_apply_3(
                    v_x_10838_,
                    v___y_10840_,
                    v___y_10841_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v_r_10863_) == 0 {
                    v_a_10864_ = leanh::lean_ctor_get(v_r_10863_, 0);
                    v_isSharedCheck_10880_ = (!leanh::lean_is_exclusive(v_r_10863_)) as u8;
                    if v_isSharedCheck_10880_ == 0 {
                        v___x_10866_ = v_r_10863_;
                        v_isShared_10867_ = v_isSharedCheck_10880_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_10864_);
                        leanh::lean_dec(v_r_10863_);
                        v___x_10866_ = leanh::lean_box(0);
                        v_isShared_10867_ = v_isSharedCheck_10880_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_10881_ = leanh::lean_ctor_get(v_r_10863_, 0);
                    leanh::lean_inc(v_a_10881_);
                    leanh::lean_dec_ref_known(v_r_10863_, 1);
                    v___x_10882_ = leanh::lean_box(0);
                    v___x_10883_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_10841_, v_isExporting_10845_, v___x_10859_, v___x_10882_);
                    v_isSharedCheck_10890_ = (!leanh::lean_is_exclusive(v___x_10883_)) as u8;
                    if v_isSharedCheck_10890_ == 0 {
                        v_unused_10891_ = leanh::lean_ctor_get(v___x_10883_, 0);
                        leanh::lean_dec(v_unused_10891_);
                        v___x_10885_ = v___x_10883_;
                        v_isShared_10886_ = v_isSharedCheck_10890_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_10883_);
                        v___x_10885_ = leanh::lean_box(0);
                        v_isShared_10886_ = v_isSharedCheck_10890_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                leanh::lean_inc(v_a_10864_);
                if v_isShared_10867_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_10866_, 1);
                    v___x_10869_ = v___x_10866_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_10879_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10879_, 0, v_a_10864_);
                    v___x_10869_ = v_reuseFailAlloc_10879_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_10870_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_10841_, v_isExporting_10845_, v___x_10859_, v___x_10869_);
                leanh::lean_dec_ref(v___x_10869_);
                v_isSharedCheck_10877_ = (!leanh::lean_is_exclusive(v___x_10870_)) as u8;
                if v_isSharedCheck_10877_ == 0 {
                    v_unused_10878_ = leanh::lean_ctor_get(v___x_10870_, 0);
                    leanh::lean_dec(v_unused_10878_);
                    v___x_10872_ = v___x_10870_;
                    v_isShared_10873_ = v_isSharedCheck_10877_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_dec(v___x_10870_);
                    v___x_10872_ = leanh::lean_box(0);
                    v_isShared_10873_ = v_isSharedCheck_10877_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_10873_ == 0 {
                    leanh::lean_ctor_set(v___x_10872_, 0, v_a_10864_);
                    v___x_10875_ = v___x_10872_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_10876_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10876_, 0, v_a_10864_);
                    v___x_10875_ = v_reuseFailAlloc_10876_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_10875_;
            }
            7 => {
                if v_isShared_10886_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_10885_, 1);
                    leanh::lean_ctor_set(v___x_10885_, 0, v_a_10881_);
                    v___x_10888_ = v___x_10885_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_10889_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10889_, 0, v_a_10881_);
                    v___x_10888_ = v_reuseFailAlloc_10889_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_10888_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___boxed(
    mut v_x_10895_: *mut leanh::LeanObject,
    mut v_isExporting_10896_: *mut leanh::LeanObject,
    mut v___y_10897_: *mut leanh::LeanObject,
    mut v___y_10898_: *mut leanh::LeanObject,
    mut v___y_10899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_10900_: u8 = 0;
    let mut v_res_10901_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_10900_ = (leanh::lean_unbox(v_isExporting_10896_) as u8);
    v_res_10901_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_10895_, v_isExporting_boxed_10900_, v___y_10897_, v___y_10898_);
    leanh::lean_dec(v___y_10898_);
    leanh::lean_dec_ref(v___y_10897_);
    return v_res_10901_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(
    mut v_x_10902_: *mut leanh::LeanObject,
    mut v_when_10903_: u8,
    mut v___y_10904_: *mut leanh::LeanObject,
    mut v___y_10905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_when_10903_ == 0 {
        let mut v___x_10907_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v___y_10905_);
        leanh::lean_inc_ref(v___y_10904_);
        v___x_10907_ = leanh::lean_apply_3(
            v_x_10902_,
            v___y_10904_,
            v___y_10905_,
            leanh::lean_box(0),
        );
        return v___x_10907_;
    } else {
        let mut v___x_10908_: u8 = 0;
        let mut v___x_10909_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_10908_ = 0;
        v___x_10909_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_10902_, v___x_10908_, v___y_10904_, v___y_10905_);
        return v___x_10909_;
    }
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg___boxed(
    mut v_x_10910_: *mut leanh::LeanObject,
    mut v_when_10911_: *mut leanh::LeanObject,
    mut v___y_10912_: *mut leanh::LeanObject,
    mut v___y_10913_: *mut leanh::LeanObject,
    mut v___y_10914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_when_boxed_10915_: u8 = 0;
    let mut v_res_10916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_10915_ = (leanh::lean_unbox(v_when_10911_) as u8);
    v_res_10916_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(
        v_x_10910_,
        v_when_boxed_10915_,
        v___y_10912_,
        v___y_10913_,
    );
    leanh::lean_dec(v___y_10913_);
    leanh::lean_dec_ref(v___y_10912_);
    return v_res_10916_;
}
pub unsafe fn l_Lean_Meta_unfoldIfArgIsAppOf(
    mut v_fnNames_10917_: *mut leanh::LeanObject,
    mut v_numSectionVars_10918_: *mut leanh::LeanObject,
    mut v_e_10919_: *mut leanh::LeanObject,
    mut v_a_10920_: *mut leanh::LeanObject,
    mut v_a_10921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_10923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_10924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10925_: u8 = 0;
    let mut v___x_10926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_10923_ = l_Lean_Core_betaReduce___closed__1;
    v___f_10924_ = leanh::lean_alloc_closure(
        l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    leanh::lean_closure_set(v___f_10924_, 0, v_fnNames_10917_);
    leanh::lean_closure_set(v___f_10924_, 1, v_numSectionVars_10918_);
    leanh::lean_closure_set(v___f_10924_, 2, v_e_10919_);
    leanh::lean_closure_set(v___f_10924_, 3, v___f_10923_);
    v___x_10925_ = 1;
    v___x_10926_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(
        v___f_10924_,
        v___x_10925_,
        v_a_10920_,
        v_a_10921_,
    );
    return v___x_10926_;
}
pub unsafe fn l_Lean_Meta_unfoldIfArgIsAppOf___boxed(
    mut v_fnNames_10927_: *mut leanh::LeanObject,
    mut v_numSectionVars_10928_: *mut leanh::LeanObject,
    mut v_e_10929_: *mut leanh::LeanObject,
    mut v_a_10930_: *mut leanh::LeanObject,
    mut v_a_10931_: *mut leanh::LeanObject,
    mut v_a_10932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_10933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_10933_ = l_Lean_Meta_unfoldIfArgIsAppOf(
        v_fnNames_10927_,
        v_numSectionVars_10928_,
        v_e_10929_,
        v_a_10930_,
        v_a_10931_,
    );
    leanh::lean_dec(v_a_10931_);
    leanh::lean_dec_ref(v_a_10930_);
    return v_res_10933_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(
    mut v_00_u03b1_10934_: *mut leanh::LeanObject,
    mut v_x_10935_: *mut leanh::LeanObject,
    mut v_isExporting_10936_: u8,
    mut v___y_10937_: *mut leanh::LeanObject,
    mut v___y_10938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10940_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_10935_, v_isExporting_10936_, v___y_10937_, v___y_10938_);
    return v___x_10940_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___boxed(
    mut v_00_u03b1_10941_: *mut leanh::LeanObject,
    mut v_x_10942_: *mut leanh::LeanObject,
    mut v_isExporting_10943_: *mut leanh::LeanObject,
    mut v___y_10944_: *mut leanh::LeanObject,
    mut v___y_10945_: *mut leanh::LeanObject,
    mut v___y_10946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_10947_: u8 = 0;
    let mut v_res_10948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_10947_ = (leanh::lean_unbox(v_isExporting_10943_) as u8);
    v_res_10948_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(v_00_u03b1_10941_, v_x_10942_, v_isExporting_boxed_10947_, v___y_10944_, v___y_10945_);
    leanh::lean_dec(v___y_10945_);
    leanh::lean_dec_ref(v___y_10944_);
    return v_res_10948_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(
    mut v_00_u03b1_10949_: *mut leanh::LeanObject,
    mut v_x_10950_: *mut leanh::LeanObject,
    mut v_when_10951_: u8,
    mut v___y_10952_: *mut leanh::LeanObject,
    mut v___y_10953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10955_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(
        v_x_10950_,
        v_when_10951_,
        v___y_10952_,
        v___y_10953_,
    );
    return v___x_10955_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___boxed(
    mut v_00_u03b1_10956_: *mut leanh::LeanObject,
    mut v_x_10957_: *mut leanh::LeanObject,
    mut v_when_10958_: *mut leanh::LeanObject,
    mut v___y_10959_: *mut leanh::LeanObject,
    mut v___y_10960_: *mut leanh::LeanObject,
    mut v___y_10961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_when_boxed_10962_: u8 = 0;
    let mut v_res_10963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_10962_ = (leanh::lean_unbox(v_when_10958_) as u8);
    v_res_10963_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(
        v_00_u03b1_10956_,
        v_x_10957_,
        v_when_boxed_10962_,
        v___y_10959_,
        v___y_10960_,
    );
    leanh::lean_dec(v___y_10960_);
    leanh::lean_dec_ref(v___y_10959_);
    return v_res_10963_;
}
pub unsafe fn l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(
    mut v_x_10964_: *mut leanh::LeanObject,
    mut v___y_10965_: *mut leanh::LeanObject,
    mut v___y_10966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10968_ = l_Lean_Core_betaReduce___lam__0___closed__0;
    v___x_10969_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_10969_, 0, v___x_10968_);
    return v___x_10969_;
}
pub unsafe fn l_Lean_Meta_eraseInaccessibleAnnotations___lam__0___boxed(
    mut v_x_10970_: *mut leanh::LeanObject,
    mut v___y_10971_: *mut leanh::LeanObject,
    mut v___y_10972_: *mut leanh::LeanObject,
    mut v___y_10973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_10974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_10974_ =
        l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(v_x_10970_, v___y_10971_, v___y_10972_);
    leanh::lean_dec(v___y_10972_);
    leanh::lean_dec_ref(v___y_10971_);
    leanh::lean_dec_ref(v_x_10970_);
    return v_res_10974_;
}
pub unsafe fn l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(
    mut v_e_10975_: *mut leanh::LeanObject,
    mut v___y_10976_: *mut leanh::LeanObject,
    mut v___y_10977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_10980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_10984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10983_ = l_Lean_inaccessible_x3f(v_e_10975_);
                if leanh::lean_obj_tag(v___x_10983_) == 1 {
                    leanh::lean_dec_ref(v_e_10975_);
                    v_val_10984_ = leanh::lean_ctor_get(v___x_10983_, 0);
                    leanh::lean_inc(v_val_10984_);
                    leanh::lean_dec_ref_known(v___x_10983_, 1);
                    v___y_10980_ = v_val_10984_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_10983_);
                    v___y_10980_ = v_e_10975_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_10981_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_10981_, 0, v___y_10980_);
                v___x_10982_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_10982_, 0, v___x_10981_);
                return v___x_10982_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_eraseInaccessibleAnnotations___lam__1___boxed(
    mut v_e_10985_: *mut leanh::LeanObject,
    mut v___y_10986_: *mut leanh::LeanObject,
    mut v___y_10987_: *mut leanh::LeanObject,
    mut v___y_10988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_10989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_10989_ =
        l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(v_e_10985_, v___y_10986_, v___y_10987_);
    leanh::lean_dec(v___y_10987_);
    leanh::lean_dec_ref(v___y_10986_);
    return v_res_10989_;
}
pub unsafe fn l_Lean_Meta_eraseInaccessibleAnnotations(
    mut v_e_10992_: *mut leanh::LeanObject,
    mut v_a_10993_: *mut leanh::LeanObject,
    mut v_a_10994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_10996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_10997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_10996_ = l_Lean_Meta_eraseInaccessibleAnnotations___closed__0;
    v___f_10997_ = l_Lean_Meta_eraseInaccessibleAnnotations___closed__1;
    v___x_10998_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(
        v_e_10992_,
        v___f_10996_,
        v___f_10997_,
        v_a_10993_,
        v_a_10994_,
    );
    return v___x_10998_;
}
pub unsafe fn l_Lean_Meta_eraseInaccessibleAnnotations___boxed(
    mut v_e_10999_: *mut leanh::LeanObject,
    mut v_a_11000_: *mut leanh::LeanObject,
    mut v_a_11001_: *mut leanh::LeanObject,
    mut v_a_11002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_11003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_11003_ = l_Lean_Meta_eraseInaccessibleAnnotations(v_e_10999_, v_a_11000_, v_a_11001_);
    leanh::lean_dec(v_a_11001_);
    leanh::lean_dec_ref(v_a_11000_);
    return v_res_11003_;
}
pub unsafe fn l_Lean_Meta_erasePatternRefAnnotations___lam__1(
    mut v_e_11004_: *mut leanh::LeanObject,
    mut v___y_11005_: *mut leanh::LeanObject,
    mut v___y_11006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_11009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_11010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_11011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_11012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_11013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_11014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_11012_ = l_Lean_patternWithRef_x3f(v_e_11004_);
                if leanh::lean_obj_tag(v___x_11012_) == 1 {
                    leanh::lean_dec_ref(v_e_11004_);
                    v_val_11013_ = leanh::lean_ctor_get(v___x_11012_, 0);
                    leanh::lean_inc(v_val_11013_);
                    leanh::lean_dec_ref_known(v___x_11012_, 1);
                    v_snd_11014_ = leanh::lean_ctor_get(v_val_11013_, 1);
                    leanh::lean_inc(v_snd_11014_);
                    leanh::lean_dec(v_val_11013_);
                    v___y_11009_ = v_snd_11014_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_11012_);
                    v___y_11009_ = v_e_11004_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_11010_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_11010_, 0, v___y_11009_);
                v___x_11011_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_11011_, 0, v___x_11010_);
                return v___x_11011_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_erasePatternRefAnnotations___lam__1___boxed(
    mut v_e_11015_: *mut leanh::LeanObject,
    mut v___y_11016_: *mut leanh::LeanObject,
    mut v___y_11017_: *mut leanh::LeanObject,
    mut v___y_11018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_11019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_11019_ =
        l_Lean_Meta_erasePatternRefAnnotations___lam__1(v_e_11015_, v___y_11016_, v___y_11017_);
    leanh::lean_dec(v___y_11017_);
    leanh::lean_dec_ref(v___y_11016_);
    return v_res_11019_;
}
pub unsafe fn l_Lean_Meta_erasePatternRefAnnotations(
    mut v_e_11021_: *mut leanh::LeanObject,
    mut v_a_11022_: *mut leanh::LeanObject,
    mut v_a_11023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_11025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_11026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_11027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_11025_ = l_Lean_Meta_eraseInaccessibleAnnotations___closed__0;
    v___f_11026_ = l_Lean_Meta_erasePatternRefAnnotations___closed__0;
    v___x_11027_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(
        v_e_11021_,
        v___f_11025_,
        v___f_11026_,
        v_a_11022_,
        v_a_11023_,
    );
    return v___x_11027_;
}
pub unsafe fn l_Lean_Meta_erasePatternRefAnnotations___boxed(
    mut v_e_11028_: *mut leanh::LeanObject,
    mut v_a_11029_: *mut leanh::LeanObject,
    mut v_a_11030_: *mut leanh::LeanObject,
    mut v_a_11031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_11032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_11032_ = l_Lean_Meta_erasePatternRefAnnotations(v_e_11028_, v_a_11029_, v_a_11030_);
    leanh::lean_dec(v_a_11030_);
    leanh::lean_dec_ref(v_a_11029_);
    return v_res_11032_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Transform(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_FunInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_instInhabitedTransformStep_default = _init_l_Lean_instInhabitedTransformStep_default();
    leanh::lean_mark_persistent(l_Lean_instInhabitedTransformStep_default);
    l_Lean_instInhabitedTransformStep = _init_l_Lean_instInhabitedTransformStep();
    leanh::lean_mark_persistent(l_Lean_instInhabitedTransformStep);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Transform(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Transform(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_FunInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Transform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Transform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Transform(builtin);
}
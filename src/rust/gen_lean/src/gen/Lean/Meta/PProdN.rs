// Lean compiler output
// Module: Lean.Meta.PProdN
// Imports: Lean.Meta.Transform Init.Data.Range.Polymorphic.Iterators Init.Omega
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get, lean_array_get_size, lean_array_pop,
    lean_array_push, lean_array_set, lean_array_size, lean_array_uget, lean_array_uget_borrowed,
    lean_array_uset, lean_expr_dbg_to_string, lean_infer_type, lean_mk_array, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_panic_fn_borrowed, lean_ptr_addr, lean_st_ref_set, lean_st_ref_take, lean_string_append,
    lean_string_dec_eq, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor,
    lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat,
    lean_usize_sub, lean_whnf,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold, l_Array_ofFn___redArg,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_maxRecDepthErrorMessage, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_panic___redArg,
};
use crate::r#gen::Init::System::CancelToken::l_IO_CancelToken_isSet;
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::System::ST::{l_ST_Prim_Ref_get___boxed, l_ST_Prim_mkRef___boxed};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_checkSystem, l_Lean_Core_instMonadCoreM___lam__0___boxed,
    l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Exception::l_Lean_interruptExceptionId;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_appFnCleanup___redArg,
    l_Lean_Expr_beta, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_const___override,
    l_Lean_Expr_forallE___override, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_isApp,
    l_Lean_Expr_isAppOfArity, l_Lean_Expr_isConstOf, l_Lean_Expr_isProj, l_Lean_Expr_isSort,
    l_Lean_Expr_lam___override, l_Lean_Expr_letE___override, l_Lean_Expr_mdata___override,
    l_Lean_Expr_proj___override, l_Lean_Expr_projExpr_x21, l_Lean_Expr_projIdx_x21,
    l_Lean_Expr_sort___override, l_Lean_Expr_sortLevel_x21, l_Lean_ExprStructEq_beq,
    l_Lean_ExprStructEq_hash, l_Lean_instBEqBinderInfo_beq, l_Lean_instInhabitedExpr,
    l_Lean_mkApp4, l_Lean_mkAppB, l_Lean_mkAppN,
};
use crate::r#gen::Lean::Level::l_Lean_Level_isAlwaysZero;
use crate::r#gen::Lean::Message::l_Lean_MessageData_ofFormat;
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux,
    l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__0___boxed,
    l_Lean_Meta_instMonadMetaM___lam__1___boxed, l_Lean_Meta_instantiateMVarsIfMVarApp___redArg,
    l_Lean_Meta_mkLambdaFVars,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::Transform::{
    initialize_Lean_Meta_Transform, runtime_initialize_Lean_Meta_Transform,
};
pub static l_Lean_Meta_mkPProd___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [80, 80, 114, 111, 100, 0],
    };
static mut l_Lean_Meta_mkPProd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkPProd___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkPProd___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkPProd___closed__0_value)
                as *mut crate::leanh::LeanObject,
            10284180294948621841 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkPProd___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkPProd___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkPProd___closed__2_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [65, 110, 100, 0],
    };
static mut l_Lean_Meta_mkPProd___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkPProd___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkPProd___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkPProd___closed__2_value)
                as *mut crate::leanh::LeanObject,
            9743492140944907313 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkPProd___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkPProd___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_mkPProd___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkPProd___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkPProdMk___closed__0_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [109, 107, 0],
    };
static mut l_Lean_Meta_mkPProdMk___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkPProdMk___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_mkPProdMk___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkPProd___closed__0_value)
                as *mut crate::leanh::LeanObject,
            10284180294948621841 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_mkPProdMk___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkPProdMk___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkPProdMk___closed__0_value)
                as *mut crate::leanh::LeanObject,
            1981777091013684029 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkPProdMk___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkPProdMk___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkPProdMk___closed__2_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [105, 110, 116, 114, 111, 0],
    };
static mut l_Lean_Meta_mkPProdMk___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkPProdMk___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_mkPProdMk___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkPProd___closed__2_value)
                as *mut crate::leanh::LeanObject,
            9743492140944907313 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_mkPProdMk___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkPProdMk___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkPProdMk___closed__2_value)
                as *mut crate::leanh::LeanObject,
            11695081953491693114 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkPProdMk___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkPProdMk___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_mkPProdMk___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkPProdMk___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkPProdFst___closed__0_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 80, 80, 114, 111, 100, 78, 0,
        ],
    };
static mut l_Lean_Meta_mkPProdFst___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkPProdFst___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkPProdFst___closed__1_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 109, 107, 80, 80, 114, 111, 100, 70, 115,
            116, 0,
        ],
    };
static mut l_Lean_Meta_mkPProdFst___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkPProdFst___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkPProdFst___closed__2_value: crate::leanh::LeanStringObject<27> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            109, 107, 80, 80, 114, 111, 100, 70, 115, 116, 58, 32, 99, 97, 110, 110, 111, 116, 32,
            104, 97, 110, 100, 108, 101, 32, 0,
        ],
    };
static mut l_Lean_Meta_mkPProdFst___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkPProdFst___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkPProdFst___closed__3_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [10, 111, 102, 32, 116, 121, 112, 101, 32, 0],
    };
static mut l_Lean_Meta_mkPProdFst___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkPProdFst___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__0_value:
    crate::leanh::LeanStringObject<48> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 48,
    m_capacity: 48,
    m_length: 47,
    m_data: [
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 80,
        80, 114, 111, 100, 78, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 109, 107,
        84, 121, 112, 101, 83, 110, 100, 0,
    ],
};
static mut l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__1_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        109, 107, 84, 121, 112, 101, 83, 110, 100, 58, 32, 99, 97, 110, 110, 111, 116, 32, 104, 97,
        110, 100, 108, 101, 32, 116, 121, 112, 101, 32, 0,
    ],
};
static mut l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkPProdSnd___closed__0_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 109, 107, 80, 80, 114, 111, 100, 83, 110,
            100, 0,
        ],
    };
static mut l_Lean_Meta_mkPProdSnd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkPProdSnd___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkPProdSnd___closed__1_value: crate::leanh::LeanStringObject<27> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            109, 107, 80, 80, 114, 111, 100, 83, 110, 100, 58, 32, 99, 97, 110, 110, 111, 116, 32,
            104, 97, 110, 100, 108, 101, 32, 0,
        ],
    };
static mut l_Lean_Meta_mkPProdSnd___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkPProdSnd___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_PProdN_genMk___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_PProdN_genMk___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_PProdN_genMk___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_PProdN_genMk___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_PProdN_genMk___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lean_Meta_PProdN_genMk___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_genMk___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_PProdN_genMk___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lean_Meta_PProdN_genMk___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_genMk___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_PProdN_genMk___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_PProdN_genMk___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_genMk___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_PProdN_genMk___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_PProdN_genMk___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_genMk___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_PProdN_genMk___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_PProdN_genMk___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_genMk___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_PProdN_genMk___redArg___closed__7_value: crate::leanh::LeanStringObject<23> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 80, 80, 114, 111, 100, 78, 46, 103, 101,
            110, 77, 107, 0,
        ],
    };
static mut l_Lean_Meta_PProdN_genMk___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_genMk___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_PProdN_genMk___redArg___closed__8_value: crate::leanh::LeanStringObject<36> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 33, 120, 115, 46, 105, 115, 69, 109, 112, 116, 121, 10, 32, 32, 0,
        ],
    };
static mut l_Lean_Meta_PProdN_genMk___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_genMk___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_PProdN_genMk___redArg___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_PProdN_genMk___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_PProdN_pack___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_mkPProd___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_PProdN_pack___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_pack___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_PProdN_pack___closed__1_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [80, 85, 110, 105, 116, 0],
    };
static mut l_Lean_Meta_PProdN_pack___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_pack___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_PProdN_pack___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_PProdN_pack___closed__1_value)
                as *mut crate::leanh::LeanObject,
            11091137386503903511 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_PProdN_pack___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_pack___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_PProdN_pack___closed__3_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [84, 114, 117, 101, 0],
    };
static mut l_Lean_Meta_PProdN_pack___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_pack___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_PProdN_pack___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_PProdN_pack___closed__3_value)
                as *mut crate::leanh::LeanObject,
            11870096045526947150 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_PProdN_pack___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_pack___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_PProdN_pack___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_PProdN_pack___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_PProdN_unpack___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_PProdN_unpack___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_unpack___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_PProdN_mk___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_mkPProdMk___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_PProdN_mk___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_mk___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_PProdN_mk___closed__1_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [117, 110, 105, 116, 0],
    };
static mut l_Lean_Meta_PProdN_mk___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_mk___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_PProdN_mk___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_PProdN_pack___closed__1_value)
                as *mut crate::leanh::LeanObject,
            11091137386503903511 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_PProdN_mk___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_PProdN_mk___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_PProdN_mk___closed__1_value)
                as *mut crate::leanh::LeanObject,
            14036392901208071058 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_PProdN_mk___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_mk___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_PProdN_mk___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_PProdN_pack___closed__3_value)
                as *mut crate::leanh::LeanObject,
            11870096045526947150 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_PProdN_mk___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_PProdN_mk___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkPProdMk___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18067798339771668657 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_PProdN_mk___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_mk___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_PProdN_mk___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_PProdN_mk___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_PProdN_packLambdas___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
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
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 80, 80, 114, 111, 100, 78, 46, 112, 97, 99,
        107, 76, 97, 109, 98, 100, 97, 115, 0,
    ],
};
static mut l_Lean_Meta_PProdN_packLambdas___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_packLambdas___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_PProdN_packLambdas___lam__0___closed__1_value:
    crate::leanh::LeanStringObject<159> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 159,
    m_capacity: 159,
    m_length: 158,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 115, 111, 114, 116, 46, 105, 115, 83, 111, 114, 116, 10, 32, 32, 32, 32, 45, 45,
        32, 78, 66, 58, 32, 85, 115, 101, 32, 98, 101, 116, 97, 44, 32, 110, 111, 116, 32, 105,
        110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 76, 97, 109, 98, 100, 97, 59, 32, 119, 104,
        101, 110, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 105, 110, 103, 32, 116, 104, 101,
        32, 98, 101, 108, 111, 119, 68, 105, 99, 116, 32, 98, 101, 108, 111, 119, 10, 32, 32, 32,
        32, 45, 45, 32, 119, 101, 32, 112, 97, 115, 115, 32, 96, 67, 96, 44, 32, 97, 32, 112, 108,
        97, 105, 110, 32, 70, 86, 97, 114, 44, 32, 104, 101, 114, 101, 10, 32, 32, 32, 32, 0,
    ],
};
static mut l_Lean_Meta_PProdN_packLambdas___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_packLambdas___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 2 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__0_value:
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
    m_data: [114, 105, 103, 104, 116, 0],
};
static mut l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_mkPProd___closed__2_value) as *mut crate::leanh::LeanObject,
        9743492140944907313 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        10515106874815532050 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__2_value:
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
    m_data: [115, 110, 100, 0],
};
static mut l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_mkPProd___closed__0_value) as *mut crate::leanh::LeanObject,
        10284180294948621841 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__3_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        5514038568476696363 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__4_value:
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
    m_data: [108, 101, 102, 116, 0],
};
static mut l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_mkPProd___closed__2_value) as *mut crate::leanh::LeanObject,
        9743492140944907313 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__5_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__4_value)
            as *mut crate::leanh::LeanObject,
        10675986705697471500 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__6_value:
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
    m_data: [102, 115, 116, 0],
};
static mut l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_mkPProd___closed__0_value) as *mut crate::leanh::LeanObject,
        10284180294948621841 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__7_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__6_value)
            as *mut crate::leanh::LeanObject,
        4297553574835827762 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7310567555909517314 as *mut crate::leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value) as *mut crate::leanh::LeanObject,273128857561458264 as *mut crate::leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 114, 97, 110, 115, 102, 111, 114, 109, 0]};
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_PProdN_reduceProjs___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_PProdN_reduceProjs___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_PProdN_reduceProjs___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_reduceProjs___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_PProdN_reduceProjs___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_PProdN_reduceProjs___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_PProdN_reduceProjs___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_PProdN_reduceProjs___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Meta_mkPProd___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1922_ = crate::leanh::lean_box(0);
    v___x_1923_ = l_Lean_Meta_mkPProd___closed__3;
    v___x_1924_ = l_Lean_Expr_const___override(v___x_1923_, v___x_1922_);
    return v___x_1924_;
}
pub unsafe fn l_Lean_Meta_mkPProd(
    mut v_e1_1925_: *mut crate::leanh::LeanObject,
    mut v_e2_1926_: *mut crate::leanh::LeanObject,
    mut v_a_1927_: *mut crate::leanh::LeanObject,
    mut v_a_1928_: *mut crate::leanh::LeanObject,
    mut v_a_1929_: *mut crate::leanh::LeanObject,
    mut v_a_1930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1938_: u8 = 0;
    let mut v___y_1940_: u8 = 0;
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: u8 = 0;
    let mut v___x_1956_: u8 = 0;
    let mut v_isSharedCheck_1957_: u8 = 0;
    let mut v_a_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1961_: u8 = 0;
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1965_: u8 = 0;
    let mut v_a_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1973_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e1_1925_);
                v___x_1932_ =
                    l_Lean_Meta_getLevel(v_e1_1925_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_);
                if crate::leanh::lean_obj_tag(v___x_1932_) == 0 {
                    v_a_1933_ = crate::leanh::lean_ctor_get(v___x_1932_, 0);
                    crate::leanh::lean_inc(v_a_1933_);
                    crate::leanh::lean_dec_ref_known(v___x_1932_, 1);
                    crate::leanh::lean_inc_ref(v_e2_1926_);
                    v___x_1934_ = l_Lean_Meta_getLevel(
                        v_e2_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1934_) == 0 {
                        v_a_1935_ = crate::leanh::lean_ctor_get(v___x_1934_, 0);
                        v_isSharedCheck_1957_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1934_)) as u8;
                        if v_isSharedCheck_1957_ == 0 {
                            v___x_1937_ = v___x_1934_;
                            v_isShared_1938_ = v_isSharedCheck_1957_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1935_);
                            crate::leanh::lean_dec(v___x_1934_);
                            v___x_1937_ = crate::leanh::lean_box(0);
                            v_isShared_1938_ = v_isSharedCheck_1957_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1933_);
                        crate::leanh::lean_dec_ref(v_e2_1926_);
                        crate::leanh::lean_dec_ref(v_e1_1925_);
                        v_a_1958_ = crate::leanh::lean_ctor_get(v___x_1934_, 0);
                        v_isSharedCheck_1965_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1934_)) as u8;
                        if v_isSharedCheck_1965_ == 0 {
                            v___x_1960_ = v___x_1934_;
                            v_isShared_1961_ = v_isSharedCheck_1965_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1958_);
                            crate::leanh::lean_dec(v___x_1934_);
                            v___x_1960_ = crate::leanh::lean_box(0);
                            v_isShared_1961_ = v_isSharedCheck_1965_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e2_1926_);
                    crate::leanh::lean_dec_ref(v_e1_1925_);
                    v_a_1966_ = crate::leanh::lean_ctor_get(v___x_1932_, 0);
                    v_isSharedCheck_1973_ = (!crate::leanh::lean_is_exclusive(v___x_1932_)) as u8;
                    if v_isSharedCheck_1973_ == 0 {
                        v___x_1968_ = v___x_1932_;
                        v_isShared_1969_ = v_isSharedCheck_1973_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1966_);
                        crate::leanh::lean_dec(v___x_1932_);
                        v___x_1968_ = crate::leanh::lean_box(0);
                        v_isShared_1969_ = v_isSharedCheck_1973_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1955_ = l_Lean_Level_isAlwaysZero(v_a_1933_);
                if v___x_1955_ == 0 {
                    v___y_1940_ = v___x_1955_;
                    state = 2;
                    continue;
                } else {
                    v___x_1956_ = l_Lean_Level_isAlwaysZero(v_a_1935_);
                    v___y_1940_ = v___x_1956_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_1940_ == 0 {
                    v___x_1941_ = l_Lean_Meta_mkPProd___closed__1;
                    v___x_1942_ = crate::leanh::lean_box(0);
                    v___x_1943_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1943_, 0, v_a_1935_);
                    crate::leanh::lean_ctor_set(v___x_1943_, 1, v___x_1942_);
                    v___x_1944_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1944_, 0, v_a_1933_);
                    crate::leanh::lean_ctor_set(v___x_1944_, 1, v___x_1943_);
                    v___x_1945_ = l_Lean_Expr_const___override(v___x_1941_, v___x_1944_);
                    v___x_1946_ = l_Lean_mkAppB(v___x_1945_, v_e1_1925_, v_e2_1926_);
                    if v_isShared_1938_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1937_, 0, v___x_1946_);
                        v___x_1948_ = v___x_1937_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1949_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1946_);
                        v___x_1948_ = v_reuseFailAlloc_1949_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1935_);
                    crate::leanh::lean_dec(v_a_1933_);
                    v___x_1950_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkPProd___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkPProd___closed__4_once),
                        _init_l_Lean_Meta_mkPProd___closed__4,
                    );
                    v___x_1951_ = l_Lean_mkAppB(v___x_1950_, v_e1_1925_, v_e2_1926_);
                    if v_isShared_1938_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1937_, 0, v___x_1951_);
                        v___x_1953_ = v___x_1937_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1954_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 0, v___x_1951_);
                        v___x_1953_ = v_reuseFailAlloc_1954_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1948_;
            }
            4 => {
                return v___x_1953_;
            }
            5 => {
                if v_isShared_1961_ == 0 {
                    v___x_1963_ = v___x_1960_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1964_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
                    v___x_1963_ = v_reuseFailAlloc_1964_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1963_;
            }
            7 => {
                if v_isShared_1969_ == 0 {
                    v___x_1971_ = v___x_1968_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1972_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
                    v___x_1971_ = v_reuseFailAlloc_1972_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1971_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkPProd___boxed(
    mut v_e1_1974_: *mut crate::leanh::LeanObject,
    mut v_e2_1975_: *mut crate::leanh::LeanObject,
    mut v_a_1976_: *mut crate::leanh::LeanObject,
    mut v_a_1977_: *mut crate::leanh::LeanObject,
    mut v_a_1978_: *mut crate::leanh::LeanObject,
    mut v_a_1979_: *mut crate::leanh::LeanObject,
    mut v_a_1980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1981_ = l_Lean_Meta_mkPProd(
        v_e1_1974_, v_e2_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_,
    );
    crate::leanh::lean_dec(v_a_1979_);
    crate::leanh::lean_dec_ref(v_a_1978_);
    crate::leanh::lean_dec(v_a_1977_);
    crate::leanh::lean_dec_ref(v_a_1976_);
    return v_res_1981_;
}
pub unsafe fn _init_l_Lean_Meta_mkPProdMk___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1990_ = crate::leanh::lean_box(0);
    v___x_1991_ = l_Lean_Meta_mkPProdMk___closed__3;
    v___x_1992_ = l_Lean_Expr_const___override(v___x_1991_, v___x_1990_);
    return v___x_1992_;
}
pub unsafe fn l_Lean_Meta_mkPProdMk(
    mut v_e1_1993_: *mut crate::leanh::LeanObject,
    mut v_e2_1994_: *mut crate::leanh::LeanObject,
    mut v_a_1995_: *mut crate::leanh::LeanObject,
    mut v_a_1996_: *mut crate::leanh::LeanObject,
    mut v_a_1997_: *mut crate::leanh::LeanObject,
    mut v_a_1998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2010_: u8 = 0;
    let mut v___y_2012_: u8 = 0;
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: u8 = 0;
    let mut v___x_2028_: u8 = 0;
    let mut v_isSharedCheck_2029_: u8 = 0;
    let mut v_a_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2033_: u8 = 0;
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2037_: u8 = 0;
    let mut v_a_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2041_: u8 = 0;
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2045_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_1998_);
                crate::leanh::lean_inc_ref(v_a_1997_);
                crate::leanh::lean_inc(v_a_1996_);
                crate::leanh::lean_inc_ref(v_a_1995_);
                crate::leanh::lean_inc_ref(v_e1_1993_);
                v___x_2000_ =
                    lean_infer_type(v_e1_1993_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_);
                if crate::leanh::lean_obj_tag(v___x_2000_) == 0 {
                    v_a_2001_ = crate::leanh::lean_ctor_get(v___x_2000_, 0);
                    crate::leanh::lean_inc(v_a_2001_);
                    crate::leanh::lean_dec_ref_known(v___x_2000_, 1);
                    crate::leanh::lean_inc(v_a_1998_);
                    crate::leanh::lean_inc_ref(v_a_1997_);
                    crate::leanh::lean_inc(v_a_1996_);
                    crate::leanh::lean_inc_ref(v_a_1995_);
                    crate::leanh::lean_inc_ref(v_e2_1994_);
                    v___x_2002_ =
                        lean_infer_type(v_e2_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_);
                    if crate::leanh::lean_obj_tag(v___x_2002_) == 0 {
                        v_a_2003_ = crate::leanh::lean_ctor_get(v___x_2002_, 0);
                        crate::leanh::lean_inc(v_a_2003_);
                        crate::leanh::lean_dec_ref_known(v___x_2002_, 1);
                        crate::leanh::lean_inc(v_a_2001_);
                        v___x_2004_ = l_Lean_Meta_getLevel(
                            v_a_2001_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2004_) == 0 {
                            v_a_2005_ = crate::leanh::lean_ctor_get(v___x_2004_, 0);
                            crate::leanh::lean_inc(v_a_2005_);
                            crate::leanh::lean_dec_ref_known(v___x_2004_, 1);
                            crate::leanh::lean_inc(v_a_2003_);
                            v___x_2006_ = l_Lean_Meta_getLevel(
                                v_a_2003_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2006_) == 0 {
                                v_a_2007_ = crate::leanh::lean_ctor_get(v___x_2006_, 0);
                                v_isSharedCheck_2029_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2006_)) as u8;
                                if v_isSharedCheck_2029_ == 0 {
                                    v___x_2009_ = v___x_2006_;
                                    v_isShared_2010_ = v_isSharedCheck_2029_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2007_);
                                    crate::leanh::lean_dec(v___x_2006_);
                                    v___x_2009_ = crate::leanh::lean_box(0);
                                    v_isShared_2010_ = v_isSharedCheck_2029_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2005_);
                                crate::leanh::lean_dec(v_a_2003_);
                                crate::leanh::lean_dec(v_a_2001_);
                                crate::leanh::lean_dec_ref(v_e2_1994_);
                                crate::leanh::lean_dec_ref(v_e1_1993_);
                                v_a_2030_ = crate::leanh::lean_ctor_get(v___x_2006_, 0);
                                v_isSharedCheck_2037_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2006_)) as u8;
                                if v_isSharedCheck_2037_ == 0 {
                                    v___x_2032_ = v___x_2006_;
                                    v_isShared_2033_ = v_isSharedCheck_2037_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2030_);
                                    crate::leanh::lean_dec(v___x_2006_);
                                    v___x_2032_ = crate::leanh::lean_box(0);
                                    v_isShared_2033_ = v_isSharedCheck_2037_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2003_);
                            crate::leanh::lean_dec(v_a_2001_);
                            crate::leanh::lean_dec_ref(v_e2_1994_);
                            crate::leanh::lean_dec_ref(v_e1_1993_);
                            v_a_2038_ = crate::leanh::lean_ctor_get(v___x_2004_, 0);
                            v_isSharedCheck_2045_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2004_)) as u8;
                            if v_isSharedCheck_2045_ == 0 {
                                v___x_2040_ = v___x_2004_;
                                v_isShared_2041_ = v_isSharedCheck_2045_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2038_);
                                crate::leanh::lean_dec(v___x_2004_);
                                v___x_2040_ = crate::leanh::lean_box(0);
                                v_isShared_2041_ = v_isSharedCheck_2045_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2001_);
                        crate::leanh::lean_dec_ref(v_e2_1994_);
                        crate::leanh::lean_dec_ref(v_e1_1993_);
                        return v___x_2002_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e2_1994_);
                    crate::leanh::lean_dec_ref(v_e1_1993_);
                    return v___x_2000_;
                }
            }
            1 => {
                v___x_2027_ = l_Lean_Level_isAlwaysZero(v_a_2005_);
                if v___x_2027_ == 0 {
                    v___y_2012_ = v___x_2027_;
                    state = 2;
                    continue;
                } else {
                    v___x_2028_ = l_Lean_Level_isAlwaysZero(v_a_2007_);
                    v___y_2012_ = v___x_2028_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_2012_ == 0 {
                    v___x_2013_ = l_Lean_Meta_mkPProdMk___closed__1;
                    v___x_2014_ = crate::leanh::lean_box(0);
                    v___x_2015_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2015_, 0, v_a_2007_);
                    crate::leanh::lean_ctor_set(v___x_2015_, 1, v___x_2014_);
                    v___x_2016_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2016_, 0, v_a_2005_);
                    crate::leanh::lean_ctor_set(v___x_2016_, 1, v___x_2015_);
                    v___x_2017_ = l_Lean_Expr_const___override(v___x_2013_, v___x_2016_);
                    v___x_2018_ =
                        l_Lean_mkApp4(v___x_2017_, v_a_2001_, v_a_2003_, v_e1_1993_, v_e2_1994_);
                    if v_isShared_2010_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2009_, 0, v___x_2018_);
                        v___x_2020_ = v___x_2009_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2021_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2018_);
                        v___x_2020_ = v_reuseFailAlloc_2021_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2007_);
                    crate::leanh::lean_dec(v_a_2005_);
                    v___x_2022_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkPProdMk___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkPProdMk___closed__4_once),
                        _init_l_Lean_Meta_mkPProdMk___closed__4,
                    );
                    v___x_2023_ =
                        l_Lean_mkApp4(v___x_2022_, v_a_2001_, v_a_2003_, v_e1_1993_, v_e2_1994_);
                    if v_isShared_2010_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2009_, 0, v___x_2023_);
                        v___x_2025_ = v___x_2009_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2026_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2023_);
                        v___x_2025_ = v_reuseFailAlloc_2026_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_2020_;
            }
            4 => {
                return v___x_2025_;
            }
            5 => {
                if v_isShared_2033_ == 0 {
                    v___x_2035_ = v___x_2032_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2036_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
                    v___x_2035_ = v_reuseFailAlloc_2036_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2035_;
            }
            7 => {
                if v_isShared_2041_ == 0 {
                    v___x_2043_ = v___x_2040_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2044_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
                    v___x_2043_ = v_reuseFailAlloc_2044_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2043_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkPProdMk___boxed(
    mut v_e1_2046_: *mut crate::leanh::LeanObject,
    mut v_e2_2047_: *mut crate::leanh::LeanObject,
    mut v_a_2048_: *mut crate::leanh::LeanObject,
    mut v_a_2049_: *mut crate::leanh::LeanObject,
    mut v_a_2050_: *mut crate::leanh::LeanObject,
    mut v_a_2051_: *mut crate::leanh::LeanObject,
    mut v_a_2052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2053_ = l_Lean_Meta_mkPProdMk(
        v_e1_2046_, v_e2_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_,
    );
    crate::leanh::lean_dec(v_a_2051_);
    crate::leanh::lean_dec_ref(v_a_2050_);
    crate::leanh::lean_dec(v_a_2049_);
    crate::leanh::lean_dec_ref(v_a_2048_);
    return v_res_2053_;
}
pub unsafe fn l_panic___at___00Lean_Meta_mkPProdFst_spec__0(
    mut v_msg_2054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2055_ = l_Lean_instInhabitedExpr;
    v___x_2056_ = lean_panic_fn_borrowed(v___x_2055_, v_msg_2054_);
    return v___x_2056_;
}
pub unsafe fn l_Lean_Meta_mkPProdFst(
    mut v_t_2061_: *mut crate::leanh::LeanObject,
    mut v_e_2062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: u8 = 0;
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: u8 = 0;
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: u8 = 0;
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: u8 = 0;
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_t_2061_);
                v___x_2077_ = l_Lean_Expr_cleanupAnnotations(v_t_2061_);
                v___x_2078_ = l_Lean_Expr_isApp(v___x_2077_);
                if v___x_2078_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2077_);
                    state = 1;
                    continue;
                } else {
                    v___x_2079_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2077_);
                    v___x_2080_ = l_Lean_Expr_isApp(v___x_2079_);
                    if v___x_2080_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2079_);
                        state = 1;
                        continue;
                    } else {
                        v___x_2081_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2079_);
                        v___x_2082_ = l_Lean_Meta_mkPProd___closed__3;
                        v___x_2083_ = l_Lean_Expr_isConstOf(v___x_2081_, v___x_2082_);
                        if v___x_2083_ == 0 {
                            v___x_2084_ = l_Lean_Meta_mkPProd___closed__1;
                            v___x_2085_ = l_Lean_Expr_isConstOf(v___x_2081_, v___x_2084_);
                            crate::leanh::lean_dec_ref(v___x_2081_);
                            if v___x_2085_ == 0 {
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_t_2061_);
                                v___x_2086_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_2087_ = l_Lean_Expr_proj___override(
                                    v___x_2084_,
                                    v___x_2086_,
                                    v_e_2062_,
                                );
                                return v___x_2087_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2081_);
                            crate::leanh::lean_dec_ref(v_t_2061_);
                            v___x_2088_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_2089_ =
                                l_Lean_Expr_proj___override(v___x_2082_, v___x_2088_, v_e_2062_);
                            return v___x_2089_;
                        }
                    }
                }
            }
            1 => {
                v___x_2064_ = l_Lean_Meta_mkPProdFst___closed__0;
                v___x_2065_ = l_Lean_Meta_mkPProdFst___closed__1;
                v___x_2066_ = crate::leanh::lean_unsigned_to_nat(60);
                v___x_2067_ = crate::leanh::lean_unsigned_to_nat(9);
                v___x_2068_ = l_Lean_Meta_mkPProdFst___closed__2;
                v___x_2069_ = lean_expr_dbg_to_string(v_e_2062_);
                crate::leanh::lean_dec_ref(v_e_2062_);
                v___x_2070_ = lean_string_append(v___x_2068_, v___x_2069_);
                crate::leanh::lean_dec_ref(v___x_2069_);
                v___x_2071_ = l_Lean_Meta_mkPProdFst___closed__3;
                v___x_2072_ = lean_string_append(v___x_2070_, v___x_2071_);
                v___x_2073_ = lean_expr_dbg_to_string(v_t_2061_);
                crate::leanh::lean_dec_ref(v_t_2061_);
                v___x_2074_ = lean_string_append(v___x_2072_, v___x_2073_);
                crate::leanh::lean_dec_ref(v___x_2073_);
                v___x_2075_ = l_mkPanicMessageWithDecl(
                    v___x_2064_,
                    v___x_2065_,
                    v___x_2066_,
                    v___x_2067_,
                    v___x_2074_,
                );
                crate::leanh::lean_dec_ref(v___x_2074_);
                v___x_2076_ = l_panic___at___00Lean_Meta_mkPProdFst_spec__0(v___x_2075_);
                return v___x_2076_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkPProdFstM(
    mut v_e_2090_: *mut crate::leanh::LeanObject,
    mut v_a_2091_: *mut crate::leanh::LeanObject,
    mut v_a_2092_: *mut crate::leanh::LeanObject,
    mut v_a_2093_: *mut crate::leanh::LeanObject,
    mut v_a_2094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2102_: u8 = 0;
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2107_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_2094_);
                crate::leanh::lean_inc_ref(v_a_2093_);
                crate::leanh::lean_inc(v_a_2092_);
                crate::leanh::lean_inc_ref(v_a_2091_);
                crate::leanh::lean_inc_ref(v_e_2090_);
                v___x_2096_ =
                    lean_infer_type(v_e_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_);
                if crate::leanh::lean_obj_tag(v___x_2096_) == 0 {
                    v_a_2097_ = crate::leanh::lean_ctor_get(v___x_2096_, 0);
                    crate::leanh::lean_inc(v_a_2097_);
                    crate::leanh::lean_dec_ref_known(v___x_2096_, 1);
                    crate::leanh::lean_inc(v_a_2094_);
                    crate::leanh::lean_inc_ref(v_a_2093_);
                    crate::leanh::lean_inc(v_a_2092_);
                    crate::leanh::lean_inc_ref(v_a_2091_);
                    v___x_2098_ = lean_whnf(v_a_2097_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_);
                    if crate::leanh::lean_obj_tag(v___x_2098_) == 0 {
                        v_a_2099_ = crate::leanh::lean_ctor_get(v___x_2098_, 0);
                        v_isSharedCheck_2107_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2098_)) as u8;
                        if v_isSharedCheck_2107_ == 0 {
                            v___x_2101_ = v___x_2098_;
                            v_isShared_2102_ = v_isSharedCheck_2107_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2099_);
                            crate::leanh::lean_dec(v___x_2098_);
                            v___x_2101_ = crate::leanh::lean_box(0);
                            v_isShared_2102_ = v_isSharedCheck_2107_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_2090_);
                        return v___x_2098_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2090_);
                    return v___x_2096_;
                }
            }
            1 => {
                v___x_2103_ = l_Lean_Meta_mkPProdFst(v_a_2099_, v_e_2090_);
                if v_isShared_2102_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2101_, 0, v___x_2103_);
                    v___x_2105_ = v___x_2101_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2106_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
                    v___x_2105_ = v_reuseFailAlloc_2106_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2105_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkPProdFstM___boxed(
    mut v_e_2108_: *mut crate::leanh::LeanObject,
    mut v_a_2109_: *mut crate::leanh::LeanObject,
    mut v_a_2110_: *mut crate::leanh::LeanObject,
    mut v_a_2111_: *mut crate::leanh::LeanObject,
    mut v_a_2112_: *mut crate::leanh::LeanObject,
    mut v_a_2113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2114_ = l_Lean_Meta_mkPProdFstM(v_e_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_);
    crate::leanh::lean_dec(v_a_2112_);
    crate::leanh::lean_dec_ref(v_a_2111_);
    crate::leanh::lean_dec(v_a_2110_);
    crate::leanh::lean_dec_ref(v_a_2109_);
    return v_res_2114_;
}
pub unsafe fn l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd(
    mut v_t_2117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: u8 = 0;
    let mut v_arg_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: u8 = 0;
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: u8 = 0;
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_t_2117_);
                v___x_2128_ = l_Lean_Expr_cleanupAnnotations(v_t_2117_);
                v___x_2129_ = l_Lean_Expr_isApp(v___x_2128_);
                if v___x_2129_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2128_);
                    state = 1;
                    continue;
                } else {
                    v_arg_2130_ = crate::leanh::lean_ctor_get(v___x_2128_, 1);
                    crate::leanh::lean_inc_ref(v_arg_2130_);
                    v___x_2131_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2128_);
                    v___x_2132_ = l_Lean_Expr_isApp(v___x_2131_);
                    if v___x_2132_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2131_);
                        crate::leanh::lean_dec_ref(v_arg_2130_);
                        state = 1;
                        continue;
                    } else {
                        v___x_2133_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2131_);
                        v___x_2134_ = l_Lean_Meta_mkPProd___closed__3;
                        v___x_2135_ = l_Lean_Expr_isConstOf(v___x_2133_, v___x_2134_);
                        if v___x_2135_ == 0 {
                            v___x_2136_ = l_Lean_Meta_mkPProd___closed__1;
                            v___x_2137_ = l_Lean_Expr_isConstOf(v___x_2133_, v___x_2136_);
                            crate::leanh::lean_dec_ref(v___x_2133_);
                            if v___x_2137_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_2130_);
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_t_2117_);
                                return v_arg_2130_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2133_);
                            crate::leanh::lean_dec_ref(v_t_2117_);
                            return v_arg_2130_;
                        }
                    }
                }
            }
            1 => {
                v___x_2119_ = l_Lean_Meta_mkPProdFst___closed__0;
                v___x_2120_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__0;
                v___x_2121_ = crate::leanh::lean_unsigned_to_nat(70);
                v___x_2122_ = crate::leanh::lean_unsigned_to_nat(9);
                v___x_2123_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd___closed__1;
                v___x_2124_ = lean_expr_dbg_to_string(v_t_2117_);
                crate::leanh::lean_dec_ref(v_t_2117_);
                v___x_2125_ = lean_string_append(v___x_2123_, v___x_2124_);
                crate::leanh::lean_dec_ref(v___x_2124_);
                v___x_2126_ = l_mkPanicMessageWithDecl(
                    v___x_2119_,
                    v___x_2120_,
                    v___x_2121_,
                    v___x_2122_,
                    v___x_2125_,
                );
                crate::leanh::lean_dec_ref(v___x_2125_);
                v___x_2127_ = l_panic___at___00Lean_Meta_mkPProdFst_spec__0(v___x_2126_);
                return v___x_2127_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkPProdSnd(
    mut v_t_2140_: *mut crate::leanh::LeanObject,
    mut v_e_2141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: u8 = 0;
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: u8 = 0;
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: u8 = 0;
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: u8 = 0;
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_t_2140_);
                v___x_2156_ = l_Lean_Expr_cleanupAnnotations(v_t_2140_);
                v___x_2157_ = l_Lean_Expr_isApp(v___x_2156_);
                if v___x_2157_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2156_);
                    state = 1;
                    continue;
                } else {
                    v___x_2158_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2156_);
                    v___x_2159_ = l_Lean_Expr_isApp(v___x_2158_);
                    if v___x_2159_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2158_);
                        state = 1;
                        continue;
                    } else {
                        v___x_2160_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2158_);
                        v___x_2161_ = l_Lean_Meta_mkPProd___closed__3;
                        v___x_2162_ = l_Lean_Expr_isConstOf(v___x_2160_, v___x_2161_);
                        if v___x_2162_ == 0 {
                            v___x_2163_ = l_Lean_Meta_mkPProd___closed__1;
                            v___x_2164_ = l_Lean_Expr_isConstOf(v___x_2160_, v___x_2163_);
                            crate::leanh::lean_dec_ref(v___x_2160_);
                            if v___x_2164_ == 0 {
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_t_2140_);
                                v___x_2165_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_2166_ = l_Lean_Expr_proj___override(
                                    v___x_2163_,
                                    v___x_2165_,
                                    v_e_2141_,
                                );
                                return v___x_2166_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2160_);
                            crate::leanh::lean_dec_ref(v_t_2140_);
                            v___x_2167_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_2168_ =
                                l_Lean_Expr_proj___override(v___x_2161_, v___x_2167_, v_e_2141_);
                            return v___x_2168_;
                        }
                    }
                }
            }
            1 => {
                v___x_2143_ = l_Lean_Meta_mkPProdFst___closed__0;
                v___x_2144_ = l_Lean_Meta_mkPProdSnd___closed__0;
                v___x_2145_ = crate::leanh::lean_unsigned_to_nat(77);
                v___x_2146_ = crate::leanh::lean_unsigned_to_nat(9);
                v___x_2147_ = l_Lean_Meta_mkPProdSnd___closed__1;
                v___x_2148_ = lean_expr_dbg_to_string(v_e_2141_);
                crate::leanh::lean_dec_ref(v_e_2141_);
                v___x_2149_ = lean_string_append(v___x_2147_, v___x_2148_);
                crate::leanh::lean_dec_ref(v___x_2148_);
                v___x_2150_ = l_Lean_Meta_mkPProdFst___closed__3;
                v___x_2151_ = lean_string_append(v___x_2149_, v___x_2150_);
                v___x_2152_ = lean_expr_dbg_to_string(v_t_2140_);
                crate::leanh::lean_dec_ref(v_t_2140_);
                v___x_2153_ = lean_string_append(v___x_2151_, v___x_2152_);
                crate::leanh::lean_dec_ref(v___x_2152_);
                v___x_2154_ = l_mkPanicMessageWithDecl(
                    v___x_2143_,
                    v___x_2144_,
                    v___x_2145_,
                    v___x_2146_,
                    v___x_2153_,
                );
                crate::leanh::lean_dec_ref(v___x_2153_);
                v___x_2155_ = l_panic___at___00Lean_Meta_mkPProdFst_spec__0(v___x_2154_);
                return v___x_2155_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkPProdSndM(
    mut v_e_2169_: *mut crate::leanh::LeanObject,
    mut v_a_2170_: *mut crate::leanh::LeanObject,
    mut v_a_2171_: *mut crate::leanh::LeanObject,
    mut v_a_2172_: *mut crate::leanh::LeanObject,
    mut v_a_2173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2181_: u8 = 0;
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2186_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_2173_);
                crate::leanh::lean_inc_ref(v_a_2172_);
                crate::leanh::lean_inc(v_a_2171_);
                crate::leanh::lean_inc_ref(v_a_2170_);
                crate::leanh::lean_inc_ref(v_e_2169_);
                v___x_2175_ =
                    lean_infer_type(v_e_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_);
                if crate::leanh::lean_obj_tag(v___x_2175_) == 0 {
                    v_a_2176_ = crate::leanh::lean_ctor_get(v___x_2175_, 0);
                    crate::leanh::lean_inc(v_a_2176_);
                    crate::leanh::lean_dec_ref_known(v___x_2175_, 1);
                    crate::leanh::lean_inc(v_a_2173_);
                    crate::leanh::lean_inc_ref(v_a_2172_);
                    crate::leanh::lean_inc(v_a_2171_);
                    crate::leanh::lean_inc_ref(v_a_2170_);
                    v___x_2177_ = lean_whnf(v_a_2176_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_);
                    if crate::leanh::lean_obj_tag(v___x_2177_) == 0 {
                        v_a_2178_ = crate::leanh::lean_ctor_get(v___x_2177_, 0);
                        v_isSharedCheck_2186_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2177_)) as u8;
                        if v_isSharedCheck_2186_ == 0 {
                            v___x_2180_ = v___x_2177_;
                            v_isShared_2181_ = v_isSharedCheck_2186_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2178_);
                            crate::leanh::lean_dec(v___x_2177_);
                            v___x_2180_ = crate::leanh::lean_box(0);
                            v_isShared_2181_ = v_isSharedCheck_2186_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_2169_);
                        return v___x_2177_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2169_);
                    return v___x_2175_;
                }
            }
            1 => {
                v___x_2182_ = l_Lean_Meta_mkPProdSnd(v_a_2178_, v_e_2169_);
                if v_isShared_2181_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2180_, 0, v___x_2182_);
                    v___x_2184_ = v___x_2180_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2185_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2182_);
                    v___x_2184_ = v_reuseFailAlloc_2185_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2184_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkPProdSndM___boxed(
    mut v_e_2187_: *mut crate::leanh::LeanObject,
    mut v_a_2188_: *mut crate::leanh::LeanObject,
    mut v_a_2189_: *mut crate::leanh::LeanObject,
    mut v_a_2190_: *mut crate::leanh::LeanObject,
    mut v_a_2191_: *mut crate::leanh::LeanObject,
    mut v_a_2192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2193_ = l_Lean_Meta_mkPProdSndM(v_e_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_);
    crate::leanh::lean_dec(v_a_2191_);
    crate::leanh::lean_dec_ref(v_a_2190_);
    crate::leanh::lean_dec(v_a_2189_);
    crate::leanh::lean_dec_ref(v_a_2188_);
    return v_res_2193_;
}
pub unsafe fn _init_l_Lean_Meta_PProdN_genMk___redArg___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2194_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_2194_;
}
pub unsafe fn _init_l_Lean_Meta_PProdN_genMk___redArg___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2195_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_PProdN_genMk___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_PProdN_genMk___redArg___closed__0_once),
        _init_l_Lean_Meta_PProdN_genMk___redArg___closed__0,
    );
    v___x_2196_ = l_StateRefT_x27_instMonad___redArg(v___x_2195_);
    return v___x_2196_;
}
pub unsafe fn _init_l_Lean_Meta_PProdN_genMk___redArg___closed__9() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2204_ = l_Lean_Meta_PProdN_genMk___redArg___closed__8;
    v___x_2205_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2206_ = crate::leanh::lean_unsigned_to_nat(90);
    v___x_2207_ = l_Lean_Meta_PProdN_genMk___redArg___closed__7;
    v___x_2208_ = l_Lean_Meta_mkPProdFst___closed__0;
    v___x_2209_ = l_mkPanicMessageWithDecl(
        v___x_2208_,
        v___x_2207_,
        v___x_2206_,
        v___x_2205_,
        v___x_2204_,
    );
    return v___x_2209_;
}
pub unsafe fn l_Lean_Meta_PProdN_genMk___redArg(
    mut v_inst_2210_: *mut crate::leanh::LeanObject,
    mut v_mk_2211_: *mut crate::leanh::LeanObject,
    mut v_xs_2212_: *mut crate::leanh::LeanObject,
    mut v_a_2213_: *mut crate::leanh::LeanObject,
    mut v_a_2214_: *mut crate::leanh::LeanObject,
    mut v_a_2215_: *mut crate::leanh::LeanObject,
    mut v_a_2216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: u8 = 0;
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2241_: u8 = 0;
    let mut v_toFunctor_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2248_: u8 = 0;
    let mut v___f_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: u8 = 0;
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: usize = 0;
    let mut v___x_2269_: usize = 0;
    let mut v___x_319__overap_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2274_: u8 = 0;
    let mut v_unused_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2276_: u8 = 0;
    let mut v_unused_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_178__overap_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2218_ = lean_array_get_size(v_xs_2212_);
                v___x_2219_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2220_ = lean_nat_dec_eq(v___x_2218_, v___x_2219_);
                if v___x_2220_ == 0 {
                    v___x_2221_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_PProdN_genMk___redArg___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_PProdN_genMk___redArg___closed__1_once),
                        _init_l_Lean_Meta_PProdN_genMk___redArg___closed__1,
                    );
                    v_toApplicative_2222_ = crate::leanh::lean_ctor_get(v___x_2221_, 0);
                    v_toFunctor_2223_ = crate::leanh::lean_ctor_get(v_toApplicative_2222_, 0);
                    v_toSeq_2224_ = crate::leanh::lean_ctor_get(v_toApplicative_2222_, 2);
                    v_toSeqLeft_2225_ = crate::leanh::lean_ctor_get(v_toApplicative_2222_, 3);
                    v_toSeqRight_2226_ = crate::leanh::lean_ctor_get(v_toApplicative_2222_, 4);
                    v___f_2227_ = l_Lean_Meta_PProdN_genMk___redArg___closed__2;
                    v___f_2228_ = l_Lean_Meta_PProdN_genMk___redArg___closed__3;
                    crate::leanh::lean_inc_ref_n(v_toFunctor_2223_, 2);
                    v___f_2229_ = crate::leanh::lean_alloc_closure(
                        l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_2229_, 0, v_toFunctor_2223_);
                    v___f_2230_ = crate::leanh::lean_alloc_closure(
                        l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_2230_, 0, v_toFunctor_2223_);
                    v___x_2231_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2231_, 0, v___f_2229_);
                    crate::leanh::lean_ctor_set(v___x_2231_, 1, v___f_2230_);
                    crate::leanh::lean_inc(v_toSeqRight_2226_);
                    v___f_2232_ = crate::leanh::lean_alloc_closure(
                        l_ReaderT_instApplicativeOfMonad___redArg___lam__1
                            as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_2232_, 0, v_toSeqRight_2226_);
                    crate::leanh::lean_inc(v_toSeqLeft_2225_);
                    v___f_2233_ = crate::leanh::lean_alloc_closure(
                        l_ReaderT_instApplicativeOfMonad___redArg___lam__3
                            as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_2233_, 0, v_toSeqLeft_2225_);
                    crate::leanh::lean_inc(v_toSeq_2224_);
                    v___f_2234_ = crate::leanh::lean_alloc_closure(
                        l_ReaderT_instApplicativeOfMonad___redArg___lam__4
                            as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_2234_, 0, v_toSeq_2224_);
                    v___x_2235_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2235_, 0, v___x_2231_);
                    crate::leanh::lean_ctor_set(v___x_2235_, 1, v___f_2227_);
                    crate::leanh::lean_ctor_set(v___x_2235_, 2, v___f_2234_);
                    crate::leanh::lean_ctor_set(v___x_2235_, 3, v___f_2233_);
                    crate::leanh::lean_ctor_set(v___x_2235_, 4, v___f_2232_);
                    v___x_2236_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2236_, 0, v___x_2235_);
                    crate::leanh::lean_ctor_set(v___x_2236_, 1, v___f_2228_);
                    v___x_2237_ = l_StateRefT_x27_instMonad___redArg(v___x_2236_);
                    v_toApplicative_2238_ = crate::leanh::lean_ctor_get(v___x_2237_, 0);
                    v_isSharedCheck_2276_ = (!crate::leanh::lean_is_exclusive(v___x_2237_)) as u8;
                    if v_isSharedCheck_2276_ == 0 {
                        v_unused_2277_ = crate::leanh::lean_ctor_get(v___x_2237_, 1);
                        crate::leanh::lean_dec(v_unused_2277_);
                        v___x_2240_ = v___x_2237_;
                        v_isShared_2241_ = v_isSharedCheck_2276_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_toApplicative_2238_);
                        crate::leanh::lean_dec(v___x_2237_);
                        v___x_2240_ = crate::leanh::lean_box(0);
                        v_isShared_2241_ = v_isSharedCheck_2276_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_xs_2212_);
                    crate::leanh::lean_dec_ref(v_mk_2211_);
                    v___f_2278_ = l_Lean_Meta_PProdN_genMk___redArg___closed__6;
                    v___x_2279_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_PProdN_genMk___redArg___closed__9),
                        core::ptr::addr_of_mut!(l_Lean_Meta_PProdN_genMk___redArg___closed__9_once),
                        _init_l_Lean_Meta_PProdN_genMk___redArg___closed__9,
                    );
                    v___x_178__overap_2280_ = l_panic___redArg(v___f_2278_, v___x_2279_);
                    crate::leanh::lean_inc(v_a_2216_);
                    crate::leanh::lean_inc_ref(v_a_2215_);
                    crate::leanh::lean_inc(v_a_2214_);
                    crate::leanh::lean_inc_ref(v_a_2213_);
                    v___x_2281_ = crate::leanh::lean_apply_5(
                        v___x_178__overap_2280_,
                        v_a_2213_,
                        v_a_2214_,
                        v_a_2215_,
                        v_a_2216_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_2281_;
                }
            }
            1 => {
                v_toFunctor_2242_ = crate::leanh::lean_ctor_get(v_toApplicative_2238_, 0);
                v_toSeq_2243_ = crate::leanh::lean_ctor_get(v_toApplicative_2238_, 2);
                v_toSeqLeft_2244_ = crate::leanh::lean_ctor_get(v_toApplicative_2238_, 3);
                v_toSeqRight_2245_ = crate::leanh::lean_ctor_get(v_toApplicative_2238_, 4);
                v_isSharedCheck_2274_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2238_)) as u8;
                if v_isSharedCheck_2274_ == 0 {
                    v_unused_2275_ = crate::leanh::lean_ctor_get(v_toApplicative_2238_, 1);
                    crate::leanh::lean_dec(v_unused_2275_);
                    v___x_2247_ = v_toApplicative_2238_;
                    v_isShared_2248_ = v_isSharedCheck_2274_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_2245_);
                    crate::leanh::lean_inc(v_toSeqLeft_2244_);
                    crate::leanh::lean_inc(v_toSeq_2243_);
                    crate::leanh::lean_inc(v_toFunctor_2242_);
                    crate::leanh::lean_dec(v_toApplicative_2238_);
                    v___x_2247_ = crate::leanh::lean_box(0);
                    v_isShared_2248_ = v_isSharedCheck_2274_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2249_ = l_Lean_Meta_PProdN_genMk___redArg___closed__4;
                v___f_2250_ = l_Lean_Meta_PProdN_genMk___redArg___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_2242_);
                v___f_2251_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2251_, 0, v_toFunctor_2242_);
                v___f_2252_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2252_, 0, v_toFunctor_2242_);
                v___x_2253_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2253_, 0, v___f_2251_);
                crate::leanh::lean_ctor_set(v___x_2253_, 1, v___f_2252_);
                v___f_2254_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2254_, 0, v_toSeqRight_2245_);
                v___f_2255_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2255_, 0, v_toSeqLeft_2244_);
                v___f_2256_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2256_, 0, v_toSeq_2243_);
                if v_isShared_2248_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2247_, 4, v___f_2254_);
                    crate::leanh::lean_ctor_set(v___x_2247_, 3, v___f_2255_);
                    crate::leanh::lean_ctor_set(v___x_2247_, 2, v___f_2256_);
                    crate::leanh::lean_ctor_set(v___x_2247_, 1, v___f_2249_);
                    crate::leanh::lean_ctor_set(v___x_2247_, 0, v___x_2253_);
                    v___x_2258_ = v___x_2247_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2273_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2253_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2273_, 1, v___f_2249_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2273_, 2, v___f_2256_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2273_, 3, v___f_2255_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2273_, 4, v___f_2254_);
                    v___x_2258_ = v_reuseFailAlloc_2273_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2241_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2240_, 1, v___f_2250_);
                    crate::leanh::lean_ctor_set(v___x_2240_, 0, v___x_2258_);
                    v___x_2260_ = v___x_2240_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2272_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2258_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2272_, 1, v___f_2250_);
                    v___x_2260_ = v_reuseFailAlloc_2272_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2261_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2262_ = lean_nat_sub(v___x_2218_, v___x_2261_);
                v___x_2263_ = lean_array_get(v_inst_2210_, v_xs_2212_, v___x_2262_);
                crate::leanh::lean_dec(v___x_2262_);
                v___x_2264_ = lean_array_pop(v_xs_2212_);
                v___x_2265_ = lean_array_get_size(v___x_2264_);
                v___x_2266_ = lean_nat_dec_lt(v___x_2219_, v___x_2265_);
                if v___x_2266_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2264_);
                    crate::leanh::lean_dec_ref(v___x_2260_);
                    crate::leanh::lean_dec_ref(v_mk_2211_);
                    v___x_2267_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2267_, 0, v___x_2263_);
                    return v___x_2267_;
                } else {
                    v___x_2268_ = lean_usize_of_nat(v___x_2265_);
                    v___x_2269_ = 0usize;
                    v___x_319__overap_2270_ =
                        l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_2260_,
                            v_mk_2211_,
                            v___x_2264_,
                            v___x_2268_,
                            v___x_2269_,
                            v___x_2263_,
                        );
                    crate::leanh::lean_inc(v_a_2216_);
                    crate::leanh::lean_inc_ref(v_a_2215_);
                    crate::leanh::lean_inc(v_a_2214_);
                    crate::leanh::lean_inc_ref(v_a_2213_);
                    v___x_2271_ = crate::leanh::lean_apply_5(
                        v___x_319__overap_2270_,
                        v_a_2213_,
                        v_a_2214_,
                        v_a_2215_,
                        v_a_2216_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_2271_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_PProdN_genMk___redArg___boxed(
    mut v_inst_2282_: *mut crate::leanh::LeanObject,
    mut v_mk_2283_: *mut crate::leanh::LeanObject,
    mut v_xs_2284_: *mut crate::leanh::LeanObject,
    mut v_a_2285_: *mut crate::leanh::LeanObject,
    mut v_a_2286_: *mut crate::leanh::LeanObject,
    mut v_a_2287_: *mut crate::leanh::LeanObject,
    mut v_a_2288_: *mut crate::leanh::LeanObject,
    mut v_a_2289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2290_ = l_Lean_Meta_PProdN_genMk___redArg(
        v_inst_2282_,
        v_mk_2283_,
        v_xs_2284_,
        v_a_2285_,
        v_a_2286_,
        v_a_2287_,
        v_a_2288_,
    );
    crate::leanh::lean_dec(v_a_2288_);
    crate::leanh::lean_dec_ref(v_a_2287_);
    crate::leanh::lean_dec(v_a_2286_);
    crate::leanh::lean_dec_ref(v_a_2285_);
    crate::leanh::lean_dec(v_inst_2282_);
    return v_res_2290_;
}
pub unsafe fn l_Lean_Meta_PProdN_genMk(
    mut v_00_u03b1_2291_: *mut crate::leanh::LeanObject,
    mut v_inst_2292_: *mut crate::leanh::LeanObject,
    mut v_mk_2293_: *mut crate::leanh::LeanObject,
    mut v_xs_2294_: *mut crate::leanh::LeanObject,
    mut v_a_2295_: *mut crate::leanh::LeanObject,
    mut v_a_2296_: *mut crate::leanh::LeanObject,
    mut v_a_2297_: *mut crate::leanh::LeanObject,
    mut v_a_2298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2300_ = l_Lean_Meta_PProdN_genMk___redArg(
        v_inst_2292_,
        v_mk_2293_,
        v_xs_2294_,
        v_a_2295_,
        v_a_2296_,
        v_a_2297_,
        v_a_2298_,
    );
    return v___x_2300_;
}
pub unsafe fn l_Lean_Meta_PProdN_genMk___boxed(
    mut v_00_u03b1_2301_: *mut crate::leanh::LeanObject,
    mut v_inst_2302_: *mut crate::leanh::LeanObject,
    mut v_mk_2303_: *mut crate::leanh::LeanObject,
    mut v_xs_2304_: *mut crate::leanh::LeanObject,
    mut v_a_2305_: *mut crate::leanh::LeanObject,
    mut v_a_2306_: *mut crate::leanh::LeanObject,
    mut v_a_2307_: *mut crate::leanh::LeanObject,
    mut v_a_2308_: *mut crate::leanh::LeanObject,
    mut v_a_2309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2310_ = l_Lean_Meta_PProdN_genMk(
        v_00_u03b1_2301_,
        v_inst_2302_,
        v_mk_2303_,
        v_xs_2304_,
        v_a_2305_,
        v_a_2306_,
        v_a_2307_,
        v_a_2308_,
    );
    crate::leanh::lean_dec(v_a_2308_);
    crate::leanh::lean_dec_ref(v_a_2307_);
    crate::leanh::lean_dec(v_a_2306_);
    crate::leanh::lean_dec_ref(v_a_2305_);
    crate::leanh::lean_dec(v_inst_2302_);
    return v_res_2310_;
}
pub unsafe fn _init_l_Lean_Meta_PProdN_pack___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2318_ = crate::leanh::lean_box(0);
    v___x_2319_ = l_Lean_Meta_PProdN_pack___closed__4;
    v___x_2320_ = l_Lean_Expr_const___override(v___x_2319_, v___x_2318_);
    return v___x_2320_;
}
pub unsafe fn l_Lean_Meta_PProdN_pack(
    mut v_lvl_2321_: *mut crate::leanh::LeanObject,
    mut v_xs_2322_: *mut crate::leanh::LeanObject,
    mut v_a_2323_: *mut crate::leanh::LeanObject,
    mut v_a_2324_: *mut crate::leanh::LeanObject,
    mut v_a_2325_: *mut crate::leanh::LeanObject,
    mut v_a_2326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: u8 = 0;
    v___x_2328_ = lean_array_get_size(v_xs_2322_);
    v___x_2329_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2330_ = lean_nat_dec_eq(v___x_2328_, v___x_2329_);
    if v___x_2330_ == 0 {
        let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_lvl_2321_);
        v___x_2331_ = l_Lean_instInhabitedExpr;
        v___x_2332_ = l_Lean_Meta_PProdN_pack___closed__0;
        v___x_2333_ = l_Lean_Meta_PProdN_genMk___redArg(
            v___x_2331_,
            v___x_2332_,
            v_xs_2322_,
            v_a_2323_,
            v_a_2324_,
            v_a_2325_,
            v_a_2326_,
        );
        return v___x_2333_;
    } else {
        let mut v___x_2334_: u8 = 0;
        crate::leanh::lean_dec_ref(v_xs_2322_);
        v___x_2334_ = l_Lean_Level_isAlwaysZero(v_lvl_2321_);
        if v___x_2334_ == 0 {
            let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2335_ = l_Lean_Meta_PProdN_pack___closed__2;
            v___x_2336_ = crate::leanh::lean_box(0);
            v___x_2337_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2337_, 0, v_lvl_2321_);
            crate::leanh::lean_ctor_set(v___x_2337_, 1, v___x_2336_);
            v___x_2338_ = l_Lean_Expr_const___override(v___x_2335_, v___x_2337_);
            v___x_2339_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2339_, 0, v___x_2338_);
            return v___x_2339_;
        } else {
            let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_lvl_2321_);
            v___x_2340_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_PProdN_pack___closed__5),
                core::ptr::addr_of_mut!(l_Lean_Meta_PProdN_pack___closed__5_once),
                _init_l_Lean_Meta_PProdN_pack___closed__5,
            );
            v___x_2341_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2341_, 0, v___x_2340_);
            return v___x_2341_;
        }
    }
}
pub unsafe fn l_Lean_Meta_PProdN_pack___boxed(
    mut v_lvl_2342_: *mut crate::leanh::LeanObject,
    mut v_xs_2343_: *mut crate::leanh::LeanObject,
    mut v_a_2344_: *mut crate::leanh::LeanObject,
    mut v_a_2345_: *mut crate::leanh::LeanObject,
    mut v_a_2346_: *mut crate::leanh::LeanObject,
    mut v_a_2347_: *mut crate::leanh::LeanObject,
    mut v_a_2348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2349_ = l_Lean_Meta_PProdN_pack(
        v_lvl_2342_,
        v_xs_2343_,
        v_a_2344_,
        v_a_2345_,
        v_a_2346_,
        v_a_2347_,
    );
    crate::leanh::lean_dec(v_a_2347_);
    crate::leanh::lean_dec_ref(v_a_2346_);
    crate::leanh::lean_dec(v_a_2345_);
    crate::leanh::lean_dec_ref(v_a_2344_);
    return v_res_2349_;
}
pub unsafe fn l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg(
    mut v_e_2350_: *mut crate::leanh::LeanObject,
    mut v_remaining_2351_: *mut crate::leanh::LeanObject,
    mut v_acc_2352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: u8 = 0;
    let mut v_fn_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: u8 = 0;
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2357_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2358_ = lean_nat_dec_eq(v_remaining_2351_, v___x_2357_);
                if v___x_2358_ == 0 {
                    if crate::leanh::lean_obj_tag(v_e_2350_) == 5 {
                        v_fn_2359_ = crate::leanh::lean_ctor_get(v_e_2350_, 0);
                        if crate::leanh::lean_obj_tag(v_fn_2359_) == 5 {
                            v_fn_2360_ = crate::leanh::lean_ctor_get(v_fn_2359_, 0);
                            if crate::leanh::lean_obj_tag(v_fn_2360_) == 4 {
                                v_declName_2361_ = crate::leanh::lean_ctor_get(v_fn_2360_, 0);
                                if crate::leanh::lean_obj_tag(v_declName_2361_) == 1 {
                                    v_pre_2362_ = crate::leanh::lean_ctor_get(v_declName_2361_, 0);
                                    if crate::leanh::lean_obj_tag(v_pre_2362_) == 0 {
                                        v_arg_2363_ = crate::leanh::lean_ctor_get(v_e_2350_, 1);
                                        v_arg_2364_ = crate::leanh::lean_ctor_get(v_fn_2359_, 1);
                                        v_str_2365_ =
                                            crate::leanh::lean_ctor_get(v_declName_2361_, 1);
                                        v___x_2366_ = l_Lean_Meta_mkPProd___closed__0;
                                        v___x_2367_ = lean_string_dec_eq(v_str_2365_, v___x_2366_);
                                        if v___x_2367_ == 0 {
                                            crate::leanh::lean_dec(v_remaining_2351_);
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc_ref(v_arg_2364_);
                                            crate::leanh::lean_inc_ref(v_arg_2363_);
                                            crate::leanh::lean_dec_ref_known(v_e_2350_, 2);
                                            v___x_2368_ = crate::leanh::lean_unsigned_to_nat(1);
                                            v___x_2369_ =
                                                lean_nat_sub(v_remaining_2351_, v___x_2368_);
                                            crate::leanh::lean_dec(v_remaining_2351_);
                                            v___x_2370_ = lean_array_push(v_acc_2352_, v_arg_2364_);
                                            v_e_2350_ = v_arg_2363_;
                                            v_remaining_2351_ = v___x_2369_;
                                            v_acc_2352_ = v___x_2370_;
                                            state = 0;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_remaining_2351_);
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_remaining_2351_);
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_remaining_2351_);
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_remaining_2351_);
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_remaining_2351_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_remaining_2351_);
                    crate::leanh::lean_dec_ref(v_e_2350_);
                    v___x_2372_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2372_, 0, v_acc_2352_);
                    return v___x_2372_;
                }
            }
            1 => {
                v___x_2355_ = lean_array_push(v_acc_2352_, v_e_2350_);
                v___x_2356_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2356_, 0, v___x_2355_);
                return v___x_2356_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg___boxed(
    mut v_e_2373_: *mut crate::leanh::LeanObject,
    mut v_remaining_2374_: *mut crate::leanh::LeanObject,
    mut v_acc_2375_: *mut crate::leanh::LeanObject,
    mut v_a_2376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2377_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg(
        v_e_2373_,
        v_remaining_2374_,
        v_acc_2375_,
    );
    return v_res_2377_;
}
pub unsafe fn l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go(
    mut v_e_2378_: *mut crate::leanh::LeanObject,
    mut v_remaining_2379_: *mut crate::leanh::LeanObject,
    mut v_acc_2380_: *mut crate::leanh::LeanObject,
    mut v_a_2381_: *mut crate::leanh::LeanObject,
    mut v_a_2382_: *mut crate::leanh::LeanObject,
    mut v_a_2383_: *mut crate::leanh::LeanObject,
    mut v_a_2384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2386_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg(
        v_e_2378_,
        v_remaining_2379_,
        v_acc_2380_,
    );
    return v___x_2386_;
}
pub unsafe fn l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___boxed(
    mut v_e_2387_: *mut crate::leanh::LeanObject,
    mut v_remaining_2388_: *mut crate::leanh::LeanObject,
    mut v_acc_2389_: *mut crate::leanh::LeanObject,
    mut v_a_2390_: *mut crate::leanh::LeanObject,
    mut v_a_2391_: *mut crate::leanh::LeanObject,
    mut v_a_2392_: *mut crate::leanh::LeanObject,
    mut v_a_2393_: *mut crate::leanh::LeanObject,
    mut v_a_2394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2395_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go(
        v_e_2387_,
        v_remaining_2388_,
        v_acc_2389_,
        v_a_2390_,
        v_a_2391_,
        v_a_2392_,
        v_a_2393_,
    );
    crate::leanh::lean_dec(v_a_2393_);
    crate::leanh::lean_dec_ref(v_a_2392_);
    crate::leanh::lean_dec(v_a_2391_);
    crate::leanh::lean_dec_ref(v_a_2390_);
    return v_res_2395_;
}
pub unsafe fn l_Lean_Meta_PProdN_unpack___redArg(
    mut v_e_2398_: *mut crate::leanh::LeanObject,
    mut v_n_2399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: u8 = 0;
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_2398_) == 4 {
                    v_declName_2407_ = crate::leanh::lean_ctor_get(v_e_2398_, 0);
                    if crate::leanh::lean_obj_tag(v_declName_2407_) == 1 {
                        v_pre_2408_ = crate::leanh::lean_ctor_get(v_declName_2407_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_2408_) == 0 {
                            v_str_2409_ = crate::leanh::lean_ctor_get(v_declName_2407_, 1);
                            v___x_2410_ = l_Lean_Meta_PProdN_pack___closed__3;
                            v___x_2411_ = lean_string_dec_eq(v_str_2409_, v___x_2410_);
                            if v___x_2411_ == 0 {
                                v___x_2412_ = l_Lean_Meta_PProdN_pack___closed__1;
                                v___x_2413_ = lean_string_dec_eq(v_str_2409_, v___x_2412_);
                                if v___x_2413_ == 0 {
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref_known(v_e_2398_, 2);
                                    crate::leanh::lean_dec(v_n_2399_);
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_2398_, 2);
                                crate::leanh::lean_dec(v_n_2399_);
                                state = 2;
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
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2402_ = l_Lean_Meta_PProdN_unpack___redArg___closed__0;
                v___x_2403_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_unpack_go___redArg(
                    v_e_2398_,
                    v_n_2399_,
                    v___x_2402_,
                );
                return v___x_2403_;
            }
            2 => {
                v___x_2405_ = l_Lean_Meta_PProdN_unpack___redArg___closed__0;
                v___x_2406_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2406_, 0, v___x_2405_);
                return v___x_2406_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_PProdN_unpack___redArg___boxed(
    mut v_e_2414_: *mut crate::leanh::LeanObject,
    mut v_n_2415_: *mut crate::leanh::LeanObject,
    mut v_a_2416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2417_ = l_Lean_Meta_PProdN_unpack___redArg(v_e_2414_, v_n_2415_);
    return v_res_2417_;
}
pub unsafe fn l_Lean_Meta_PProdN_unpack(
    mut v_e_2418_: *mut crate::leanh::LeanObject,
    mut v_n_2419_: *mut crate::leanh::LeanObject,
    mut v_a_2420_: *mut crate::leanh::LeanObject,
    mut v_a_2421_: *mut crate::leanh::LeanObject,
    mut v_a_2422_: *mut crate::leanh::LeanObject,
    mut v_a_2423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2425_ = l_Lean_Meta_PProdN_unpack___redArg(v_e_2418_, v_n_2419_);
    return v___x_2425_;
}
pub unsafe fn l_Lean_Meta_PProdN_unpack___boxed(
    mut v_e_2426_: *mut crate::leanh::LeanObject,
    mut v_n_2427_: *mut crate::leanh::LeanObject,
    mut v_a_2428_: *mut crate::leanh::LeanObject,
    mut v_a_2429_: *mut crate::leanh::LeanObject,
    mut v_a_2430_: *mut crate::leanh::LeanObject,
    mut v_a_2431_: *mut crate::leanh::LeanObject,
    mut v_a_2432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2433_ = l_Lean_Meta_PProdN_unpack(
        v_e_2426_, v_n_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_,
    );
    crate::leanh::lean_dec(v_a_2431_);
    crate::leanh::lean_dec_ref(v_a_2430_);
    crate::leanh::lean_dec(v_a_2429_);
    crate::leanh::lean_dec_ref(v_a_2428_);
    return v_res_2433_;
}
pub unsafe fn _init_l_Lean_Meta_PProdN_mk___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2442_ = crate::leanh::lean_box(0);
    v___x_2443_ = l_Lean_Meta_PProdN_mk___closed__3;
    v___x_2444_ = l_Lean_Expr_const___override(v___x_2443_, v___x_2442_);
    return v___x_2444_;
}
pub unsafe fn l_Lean_Meta_PProdN_mk(
    mut v_lvl_2445_: *mut crate::leanh::LeanObject,
    mut v_xs_2446_: *mut crate::leanh::LeanObject,
    mut v_a_2447_: *mut crate::leanh::LeanObject,
    mut v_a_2448_: *mut crate::leanh::LeanObject,
    mut v_a_2449_: *mut crate::leanh::LeanObject,
    mut v_a_2450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: u8 = 0;
    v___x_2452_ = lean_array_get_size(v_xs_2446_);
    v___x_2453_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2454_ = lean_nat_dec_eq(v___x_2452_, v___x_2453_);
    if v___x_2454_ == 0 {
        let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_lvl_2445_);
        v___x_2455_ = l_Lean_instInhabitedExpr;
        v___x_2456_ = l_Lean_Meta_PProdN_mk___closed__0;
        v___x_2457_ = l_Lean_Meta_PProdN_genMk___redArg(
            v___x_2455_,
            v___x_2456_,
            v_xs_2446_,
            v_a_2447_,
            v_a_2448_,
            v_a_2449_,
            v_a_2450_,
        );
        return v___x_2457_;
    } else {
        let mut v___x_2458_: u8 = 0;
        crate::leanh::lean_dec_ref(v_xs_2446_);
        v___x_2458_ = l_Lean_Level_isAlwaysZero(v_lvl_2445_);
        if v___x_2458_ == 0 {
            let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2459_ = l_Lean_Meta_PProdN_mk___closed__2;
            v___x_2460_ = crate::leanh::lean_box(0);
            v___x_2461_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2461_, 0, v_lvl_2445_);
            crate::leanh::lean_ctor_set(v___x_2461_, 1, v___x_2460_);
            v___x_2462_ = l_Lean_Expr_const___override(v___x_2459_, v___x_2461_);
            v___x_2463_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2463_, 0, v___x_2462_);
            return v___x_2463_;
        } else {
            let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_lvl_2445_);
            v___x_2464_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_PProdN_mk___closed__4),
                core::ptr::addr_of_mut!(l_Lean_Meta_PProdN_mk___closed__4_once),
                _init_l_Lean_Meta_PProdN_mk___closed__4,
            );
            v___x_2465_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2465_, 0, v___x_2464_);
            return v___x_2465_;
        }
    }
}
pub unsafe fn l_Lean_Meta_PProdN_mk___boxed(
    mut v_lvl_2466_: *mut crate::leanh::LeanObject,
    mut v_xs_2467_: *mut crate::leanh::LeanObject,
    mut v_a_2468_: *mut crate::leanh::LeanObject,
    mut v_a_2469_: *mut crate::leanh::LeanObject,
    mut v_a_2470_: *mut crate::leanh::LeanObject,
    mut v_a_2471_: *mut crate::leanh::LeanObject,
    mut v_a_2472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2473_ = l_Lean_Meta_PProdN_mk(
        v_lvl_2466_,
        v_xs_2467_,
        v_a_2468_,
        v_a_2469_,
        v_a_2470_,
        v_a_2471_,
    );
    crate::leanh::lean_dec(v_a_2471_);
    crate::leanh::lean_dec_ref(v_a_2470_);
    crate::leanh::lean_dec(v_a_2469_);
    crate::leanh::lean_dec_ref(v_a_2468_);
    return v_res_2473_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg(
    mut v_upperBound_2474_: *mut crate::leanh::LeanObject,
    mut v_a_2475_: *mut crate::leanh::LeanObject,
    mut v_b_2476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2477_: u8 = 0;
    let mut v_fst_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2482_: u8 = 0;
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2491_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2477_ = lean_nat_dec_lt(v_a_2475_, v_upperBound_2474_);
                if v___x_2477_ == 0 {
                    crate::leanh::lean_dec(v_a_2475_);
                    return v_b_2476_;
                } else {
                    v_fst_2478_ = crate::leanh::lean_ctor_get(v_b_2476_, 0);
                    v_snd_2479_ = crate::leanh::lean_ctor_get(v_b_2476_, 1);
                    v_isSharedCheck_2491_ = (!crate::leanh::lean_is_exclusive(v_b_2476_)) as u8;
                    if v_isSharedCheck_2491_ == 0 {
                        v___x_2481_ = v_b_2476_;
                        v_isShared_2482_ = v_isSharedCheck_2491_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2479_);
                        crate::leanh::lean_inc(v_fst_2478_);
                        crate::leanh::lean_dec(v_b_2476_);
                        v___x_2481_ = crate::leanh::lean_box(0);
                        v_isShared_2482_ = v_isSharedCheck_2491_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_fst_2478_);
                v___x_2483_ = l_Lean_Meta_mkPProdSnd(v_fst_2478_, v_snd_2479_);
                v___x_2484_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_mkTypeSnd(v_fst_2478_);
                if v_isShared_2482_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2481_, 1, v___x_2483_);
                    crate::leanh::lean_ctor_set(v___x_2481_, 0, v___x_2484_);
                    v___x_2486_ = v___x_2481_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2490_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2484_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2490_, 1, v___x_2483_);
                    v___x_2486_ = v_reuseFailAlloc_2490_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2487_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2488_ = lean_nat_add(v_a_2475_, v___x_2487_);
                crate::leanh::lean_dec(v_a_2475_);
                v_a_2475_ = v___x_2488_;
                v_b_2476_ = v___x_2486_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg___boxed(
    mut v_upperBound_2492_: *mut crate::leanh::LeanObject,
    mut v_a_2493_: *mut crate::leanh::LeanObject,
    mut v_b_2494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2495_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg(
        v_upperBound_2492_,
        v_a_2493_,
        v_b_2494_,
    );
    crate::leanh::lean_dec(v_upperBound_2492_);
    return v_res_2495_;
}
pub unsafe fn l_Lean_Meta_PProdN_proj(
    mut v_n_2496_: *mut crate::leanh::LeanObject,
    mut v_i_2497_: *mut crate::leanh::LeanObject,
    mut v_t_2498_: *mut crate::leanh::LeanObject,
    mut v_e_2499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: u8 = 0;
    v___x_2500_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2501_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2501_, 0, v_t_2498_);
    crate::leanh::lean_ctor_set(v___x_2501_, 1, v_e_2499_);
    v___x_2502_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg(
        v_i_2497_,
        v___x_2500_,
        v___x_2501_,
    );
    v_fst_2503_ = crate::leanh::lean_ctor_get(v___x_2502_, 0);
    crate::leanh::lean_inc(v_fst_2503_);
    v_snd_2504_ = crate::leanh::lean_ctor_get(v___x_2502_, 1);
    crate::leanh::lean_inc(v_snd_2504_);
    crate::leanh::lean_dec_ref(v___x_2502_);
    v___x_2505_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2506_ = lean_nat_add(v_i_2497_, v___x_2505_);
    v___x_2507_ = lean_nat_dec_lt(v___x_2506_, v_n_2496_);
    crate::leanh::lean_dec(v___x_2506_);
    if v___x_2507_ == 0 {
        crate::leanh::lean_dec(v_fst_2503_);
        return v_snd_2504_;
    } else {
        let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2508_ = l_Lean_Meta_mkPProdFst(v_fst_2503_, v_snd_2504_);
        return v___x_2508_;
    }
}
pub unsafe fn l_Lean_Meta_PProdN_proj___boxed(
    mut v_n_2509_: *mut crate::leanh::LeanObject,
    mut v_i_2510_: *mut crate::leanh::LeanObject,
    mut v_t_2511_: *mut crate::leanh::LeanObject,
    mut v_e_2512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2513_ = l_Lean_Meta_PProdN_proj(v_n_2509_, v_i_2510_, v_t_2511_, v_e_2512_);
    crate::leanh::lean_dec(v_i_2510_);
    crate::leanh::lean_dec(v_n_2509_);
    return v_res_2513_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0(
    mut v_upperBound_2514_: *mut crate::leanh::LeanObject,
    mut v_inst_2515_: *mut crate::leanh::LeanObject,
    mut v_R_2516_: *mut crate::leanh::LeanObject,
    mut v_a_2517_: *mut crate::leanh::LeanObject,
    mut v_b_2518_: *mut crate::leanh::LeanObject,
    mut v_c_2519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2520_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___redArg(
        v_upperBound_2514_,
        v_a_2517_,
        v_b_2518_,
    );
    return v___x_2520_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0___boxed(
    mut v_upperBound_2521_: *mut crate::leanh::LeanObject,
    mut v_inst_2522_: *mut crate::leanh::LeanObject,
    mut v_R_2523_: *mut crate::leanh::LeanObject,
    mut v_a_2524_: *mut crate::leanh::LeanObject,
    mut v_b_2525_: *mut crate::leanh::LeanObject,
    mut v_c_2526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2527_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_proj_spec__0(
        v_upperBound_2521_,
        v_inst_2522_,
        v_R_2523_,
        v_a_2524_,
        v_b_2525_,
        v_c_2526_,
    );
    crate::leanh::lean_dec(v_upperBound_2521_);
    return v_res_2527_;
}
pub unsafe fn l_Lean_Meta_PProdN_projs___lam__0(
    mut v_n_2528_: *mut crate::leanh::LeanObject,
    mut v_t_2529_: *mut crate::leanh::LeanObject,
    mut v_e_2530_: *mut crate::leanh::LeanObject,
    mut v_i_2531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2532_ = l_Lean_Meta_PProdN_proj(v_n_2528_, v_i_2531_, v_t_2529_, v_e_2530_);
    return v___x_2532_;
}
pub unsafe fn l_Lean_Meta_PProdN_projs___lam__0___boxed(
    mut v_n_2533_: *mut crate::leanh::LeanObject,
    mut v_t_2534_: *mut crate::leanh::LeanObject,
    mut v_e_2535_: *mut crate::leanh::LeanObject,
    mut v_i_2536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2537_ = l_Lean_Meta_PProdN_projs___lam__0(v_n_2533_, v_t_2534_, v_e_2535_, v_i_2536_);
    crate::leanh::lean_dec(v_i_2536_);
    crate::leanh::lean_dec(v_n_2533_);
    return v_res_2537_;
}
pub unsafe fn l_Lean_Meta_PProdN_projs(
    mut v_n_2538_: *mut crate::leanh::LeanObject,
    mut v_t_2539_: *mut crate::leanh::LeanObject,
    mut v_e_2540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_n_2538_);
    v___f_2541_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_PProdN_projs___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2541_, 0, v_n_2538_);
    crate::leanh::lean_closure_set(v___f_2541_, 1, v_t_2539_);
    crate::leanh::lean_closure_set(v___f_2541_, 2, v_e_2540_);
    v___x_2542_ = l_Array_ofFn___redArg(v_n_2538_, v___f_2541_);
    return v___x_2542_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg(
    mut v_upperBound_2543_: *mut crate::leanh::LeanObject,
    mut v_a_2544_: *mut crate::leanh::LeanObject,
    mut v_b_2545_: *mut crate::leanh::LeanObject,
    mut v___y_2546_: *mut crate::leanh::LeanObject,
    mut v___y_2547_: *mut crate::leanh::LeanObject,
    mut v___y_2548_: *mut crate::leanh::LeanObject,
    mut v___y_2549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2551_: u8 = 0;
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2551_ = lean_nat_dec_lt(v_a_2544_, v_upperBound_2543_);
                if v___x_2551_ == 0 {
                    crate::leanh::lean_dec(v_a_2544_);
                    v___x_2552_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2552_, 0, v_b_2545_);
                    return v___x_2552_;
                } else {
                    v___x_2553_ = l_Lean_Meta_mkPProdSndM(
                        v_b_2545_,
                        v___y_2546_,
                        v___y_2547_,
                        v___y_2548_,
                        v___y_2549_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2553_) == 0 {
                        v_a_2554_ = crate::leanh::lean_ctor_get(v___x_2553_, 0);
                        crate::leanh::lean_inc(v_a_2554_);
                        crate::leanh::lean_dec_ref_known(v___x_2553_, 1);
                        v___x_2555_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2556_ = lean_nat_add(v_a_2544_, v___x_2555_);
                        crate::leanh::lean_dec(v_a_2544_);
                        v_a_2544_ = v___x_2556_;
                        v_b_2545_ = v_a_2554_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_2544_);
                        return v___x_2553_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg___boxed(
    mut v_upperBound_2558_: *mut crate::leanh::LeanObject,
    mut v_a_2559_: *mut crate::leanh::LeanObject,
    mut v_b_2560_: *mut crate::leanh::LeanObject,
    mut v___y_2561_: *mut crate::leanh::LeanObject,
    mut v___y_2562_: *mut crate::leanh::LeanObject,
    mut v___y_2563_: *mut crate::leanh::LeanObject,
    mut v___y_2564_: *mut crate::leanh::LeanObject,
    mut v___y_2565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2566_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg(
        v_upperBound_2558_,
        v_a_2559_,
        v_b_2560_,
        v___y_2561_,
        v___y_2562_,
        v___y_2563_,
        v___y_2564_,
    );
    crate::leanh::lean_dec(v___y_2564_);
    crate::leanh::lean_dec_ref(v___y_2563_);
    crate::leanh::lean_dec(v___y_2562_);
    crate::leanh::lean_dec_ref(v___y_2561_);
    crate::leanh::lean_dec(v_upperBound_2558_);
    return v_res_2566_;
}
pub unsafe fn l_Lean_Meta_PProdN_projM(
    mut v_n_2567_: *mut crate::leanh::LeanObject,
    mut v_i_2568_: *mut crate::leanh::LeanObject,
    mut v_e_2569_: *mut crate::leanh::LeanObject,
    mut v_a_2570_: *mut crate::leanh::LeanObject,
    mut v_a_2571_: *mut crate::leanh::LeanObject,
    mut v_a_2572_: *mut crate::leanh::LeanObject,
    mut v_a_2573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2575_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2576_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg(
        v_i_2568_,
        v___x_2575_,
        v_e_2569_,
        v_a_2570_,
        v_a_2571_,
        v_a_2572_,
        v_a_2573_,
    );
    if crate::leanh::lean_obj_tag(v___x_2576_) == 0 {
        let mut v_a_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2580_: u8 = 0;
        v_a_2577_ = crate::leanh::lean_ctor_get(v___x_2576_, 0);
        crate::leanh::lean_inc(v_a_2577_);
        v___x_2578_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_2579_ = lean_nat_add(v_i_2568_, v___x_2578_);
        v___x_2580_ = lean_nat_dec_lt(v___x_2579_, v_n_2567_);
        crate::leanh::lean_dec(v___x_2579_);
        if v___x_2580_ == 0 {
            crate::leanh::lean_dec(v_a_2577_);
            return v___x_2576_;
        } else {
            let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_2576_, 1);
            v___x_2581_ =
                l_Lean_Meta_mkPProdFstM(v_a_2577_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_);
            return v___x_2581_;
        }
    } else {
        return v___x_2576_;
    }
}
pub unsafe fn l_Lean_Meta_PProdN_projM___boxed(
    mut v_n_2582_: *mut crate::leanh::LeanObject,
    mut v_i_2583_: *mut crate::leanh::LeanObject,
    mut v_e_2584_: *mut crate::leanh::LeanObject,
    mut v_a_2585_: *mut crate::leanh::LeanObject,
    mut v_a_2586_: *mut crate::leanh::LeanObject,
    mut v_a_2587_: *mut crate::leanh::LeanObject,
    mut v_a_2588_: *mut crate::leanh::LeanObject,
    mut v_a_2589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2590_ = l_Lean_Meta_PProdN_projM(
        v_n_2582_, v_i_2583_, v_e_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_,
    );
    crate::leanh::lean_dec(v_a_2588_);
    crate::leanh::lean_dec_ref(v_a_2587_);
    crate::leanh::lean_dec(v_a_2586_);
    crate::leanh::lean_dec_ref(v_a_2585_);
    crate::leanh::lean_dec(v_i_2583_);
    crate::leanh::lean_dec(v_n_2582_);
    return v_res_2590_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0(
    mut v_upperBound_2591_: *mut crate::leanh::LeanObject,
    mut v_inst_2592_: *mut crate::leanh::LeanObject,
    mut v_R_2593_: *mut crate::leanh::LeanObject,
    mut v_a_2594_: *mut crate::leanh::LeanObject,
    mut v_b_2595_: *mut crate::leanh::LeanObject,
    mut v_c_2596_: *mut crate::leanh::LeanObject,
    mut v___y_2597_: *mut crate::leanh::LeanObject,
    mut v___y_2598_: *mut crate::leanh::LeanObject,
    mut v___y_2599_: *mut crate::leanh::LeanObject,
    mut v___y_2600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2602_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___redArg(
        v_upperBound_2591_,
        v_a_2594_,
        v_b_2595_,
        v___y_2597_,
        v___y_2598_,
        v___y_2599_,
        v___y_2600_,
    );
    return v___x_2602_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0___boxed(
    mut v_upperBound_2603_: *mut crate::leanh::LeanObject,
    mut v_inst_2604_: *mut crate::leanh::LeanObject,
    mut v_R_2605_: *mut crate::leanh::LeanObject,
    mut v_a_2606_: *mut crate::leanh::LeanObject,
    mut v_b_2607_: *mut crate::leanh::LeanObject,
    mut v_c_2608_: *mut crate::leanh::LeanObject,
    mut v___y_2609_: *mut crate::leanh::LeanObject,
    mut v___y_2610_: *mut crate::leanh::LeanObject,
    mut v___y_2611_: *mut crate::leanh::LeanObject,
    mut v___y_2612_: *mut crate::leanh::LeanObject,
    mut v___y_2613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2614_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_PProdN_projM_spec__0(
        v_upperBound_2603_,
        v_inst_2604_,
        v_R_2605_,
        v_a_2606_,
        v_b_2607_,
        v_c_2608_,
        v___y_2609_,
        v___y_2610_,
        v___y_2611_,
        v___y_2612_,
    );
    crate::leanh::lean_dec(v___y_2612_);
    crate::leanh::lean_dec_ref(v___y_2611_);
    crate::leanh::lean_dec(v___y_2610_);
    crate::leanh::lean_dec_ref(v___y_2609_);
    crate::leanh::lean_dec(v_upperBound_2603_);
    return v_res_2614_;
}
pub unsafe fn l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0(
    mut v_msg_2615_: *mut crate::leanh::LeanObject,
    mut v___y_2616_: *mut crate::leanh::LeanObject,
    mut v___y_2617_: *mut crate::leanh::LeanObject,
    mut v___y_2618_: *mut crate::leanh::LeanObject,
    mut v___y_2619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407__overap_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2621_ = l_Lean_Meta_PProdN_genMk___redArg___closed__6;
    v___x_407__overap_2622_ = lean_panic_fn_borrowed(v___f_2621_, v_msg_2615_);
    crate::leanh::lean_inc(v___y_2619_);
    crate::leanh::lean_inc_ref(v___y_2618_);
    crate::leanh::lean_inc(v___y_2617_);
    crate::leanh::lean_inc_ref(v___y_2616_);
    v___x_2623_ = crate::leanh::lean_apply_5(
        v___x_407__overap_2622_,
        v___y_2616_,
        v___y_2617_,
        v___y_2618_,
        v___y_2619_,
        crate::leanh::lean_box(0),
    );
    return v___x_2623_;
}
pub unsafe fn l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0___boxed(
    mut v_msg_2624_: *mut crate::leanh::LeanObject,
    mut v___y_2625_: *mut crate::leanh::LeanObject,
    mut v___y_2626_: *mut crate::leanh::LeanObject,
    mut v___y_2627_: *mut crate::leanh::LeanObject,
    mut v___y_2628_: *mut crate::leanh::LeanObject,
    mut v___y_2629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2630_ = l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0(
        v_msg_2624_,
        v___y_2625_,
        v___y_2626_,
        v___y_2627_,
        v___y_2628_,
    );
    crate::leanh::lean_dec(v___y_2628_);
    crate::leanh::lean_dec_ref(v___y_2627_);
    crate::leanh::lean_dec(v___y_2626_);
    crate::leanh::lean_dec_ref(v___y_2625_);
    return v_res_2630_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0(
    mut v_k_2631_: *mut crate::leanh::LeanObject,
    mut v_b_2632_: *mut crate::leanh::LeanObject,
    mut v_c_2633_: *mut crate::leanh::LeanObject,
    mut v___y_2634_: *mut crate::leanh::LeanObject,
    mut v___y_2635_: *mut crate::leanh::LeanObject,
    mut v___y_2636_: *mut crate::leanh::LeanObject,
    mut v___y_2637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_2637_);
    crate::leanh::lean_inc_ref(v___y_2636_);
    crate::leanh::lean_inc(v___y_2635_);
    crate::leanh::lean_inc_ref(v___y_2634_);
    v___x_2639_ = crate::leanh::lean_apply_7(
        v_k_2631_,
        v_b_2632_,
        v_c_2633_,
        v___y_2634_,
        v___y_2635_,
        v___y_2636_,
        v___y_2637_,
        crate::leanh::lean_box(0),
    );
    return v___x_2639_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0___boxed(
    mut v_k_2640_: *mut crate::leanh::LeanObject,
    mut v_b_2641_: *mut crate::leanh::LeanObject,
    mut v_c_2642_: *mut crate::leanh::LeanObject,
    mut v___y_2643_: *mut crate::leanh::LeanObject,
    mut v___y_2644_: *mut crate::leanh::LeanObject,
    mut v___y_2645_: *mut crate::leanh::LeanObject,
    mut v___y_2646_: *mut crate::leanh::LeanObject,
    mut v___y_2647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2648_ =
        l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0(
            v_k_2640_,
            v_b_2641_,
            v_c_2642_,
            v___y_2643_,
            v___y_2644_,
            v___y_2645_,
            v___y_2646_,
        );
    crate::leanh::lean_dec(v___y_2646_);
    crate::leanh::lean_dec_ref(v___y_2645_);
    crate::leanh::lean_dec(v___y_2644_);
    crate::leanh::lean_dec_ref(v___y_2643_);
    return v_res_2648_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(
    mut v_type_2649_: *mut crate::leanh::LeanObject,
    mut v_k_2650_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2651_: u8,
    mut v___y_2652_: *mut crate::leanh::LeanObject,
    mut v___y_2653_: *mut crate::leanh::LeanObject,
    mut v___y_2654_: *mut crate::leanh::LeanObject,
    mut v___y_2655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: u8 = 0;
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2664_: u8 = 0;
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2668_: u8 = 0;
    let mut v_a_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2672_: u8 = 0;
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2676_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2657_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_2657_, 0, v_k_2650_);
                v___x_2658_ = 0;
                v___x_2659_ = crate::leanh::lean_box(0);
                v___x_2660_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        crate::leanh::lean_box(0),
                        v___x_2658_,
                        v___x_2659_,
                        v_type_2649_,
                        v___f_2657_,
                        v_cleanupAnnotations_2651_,
                        v___x_2658_,
                        v___y_2652_,
                        v___y_2653_,
                        v___y_2654_,
                        v___y_2655_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2660_) == 0 {
                    v_a_2661_ = crate::leanh::lean_ctor_get(v___x_2660_, 0);
                    v_isSharedCheck_2668_ = (!crate::leanh::lean_is_exclusive(v___x_2660_)) as u8;
                    if v_isSharedCheck_2668_ == 0 {
                        v___x_2663_ = v___x_2660_;
                        v_isShared_2664_ = v_isSharedCheck_2668_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2661_);
                        crate::leanh::lean_dec(v___x_2660_);
                        v___x_2663_ = crate::leanh::lean_box(0);
                        v_isShared_2664_ = v_isSharedCheck_2668_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2669_ = crate::leanh::lean_ctor_get(v___x_2660_, 0);
                    v_isSharedCheck_2676_ = (!crate::leanh::lean_is_exclusive(v___x_2660_)) as u8;
                    if v_isSharedCheck_2676_ == 0 {
                        v___x_2671_ = v___x_2660_;
                        v_isShared_2672_ = v_isSharedCheck_2676_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2669_);
                        crate::leanh::lean_dec(v___x_2660_);
                        v___x_2671_ = crate::leanh::lean_box(0);
                        v_isShared_2672_ = v_isSharedCheck_2676_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2664_ == 0 {
                    v___x_2666_ = v___x_2663_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2667_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
                    v___x_2666_ = v_reuseFailAlloc_2667_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2666_;
            }
            3 => {
                if v_isShared_2672_ == 0 {
                    v___x_2674_ = v___x_2671_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2675_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2669_);
                    v___x_2674_ = v_reuseFailAlloc_2675_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2674_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg___boxed(
    mut v_type_2677_: *mut crate::leanh::LeanObject,
    mut v_k_2678_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2679_: *mut crate::leanh::LeanObject,
    mut v___y_2680_: *mut crate::leanh::LeanObject,
    mut v___y_2681_: *mut crate::leanh::LeanObject,
    mut v___y_2682_: *mut crate::leanh::LeanObject,
    mut v___y_2683_: *mut crate::leanh::LeanObject,
    mut v___y_2684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2685_: u8 = 0;
    let mut v_res_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2685_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_2679_) as u8);
    v_res_2686_ =
        l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(
            v_type_2677_,
            v_k_2678_,
            v_cleanupAnnotations_boxed_2685_,
            v___y_2680_,
            v___y_2681_,
            v___y_2682_,
            v___y_2683_,
        );
    crate::leanh::lean_dec(v___y_2683_);
    crate::leanh::lean_dec_ref(v___y_2682_);
    crate::leanh::lean_dec(v___y_2681_);
    crate::leanh::lean_dec_ref(v___y_2680_);
    return v_res_2686_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2(
    mut v_00_u03b1_2687_: *mut crate::leanh::LeanObject,
    mut v_type_2688_: *mut crate::leanh::LeanObject,
    mut v_k_2689_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2690_: u8,
    mut v___y_2691_: *mut crate::leanh::LeanObject,
    mut v___y_2692_: *mut crate::leanh::LeanObject,
    mut v___y_2693_: *mut crate::leanh::LeanObject,
    mut v___y_2694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2696_ =
        l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(
            v_type_2688_,
            v_k_2689_,
            v_cleanupAnnotations_2690_,
            v___y_2691_,
            v___y_2692_,
            v___y_2693_,
            v___y_2694_,
        );
    return v___x_2696_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___boxed(
    mut v_00_u03b1_2697_: *mut crate::leanh::LeanObject,
    mut v_type_2698_: *mut crate::leanh::LeanObject,
    mut v_k_2699_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2700_: *mut crate::leanh::LeanObject,
    mut v___y_2701_: *mut crate::leanh::LeanObject,
    mut v___y_2702_: *mut crate::leanh::LeanObject,
    mut v___y_2703_: *mut crate::leanh::LeanObject,
    mut v___y_2704_: *mut crate::leanh::LeanObject,
    mut v___y_2705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2706_: u8 = 0;
    let mut v_res_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2706_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_2700_) as u8);
    v_res_2707_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2(
        v_00_u03b1_2697_,
        v_type_2698_,
        v_k_2699_,
        v_cleanupAnnotations_boxed_2706_,
        v___y_2701_,
        v___y_2702_,
        v___y_2703_,
        v___y_2704_,
    );
    crate::leanh::lean_dec(v___y_2704_);
    crate::leanh::lean_dec_ref(v___y_2703_);
    crate::leanh::lean_dec(v___y_2702_);
    crate::leanh::lean_dec_ref(v___y_2701_);
    return v_res_2707_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1(
    mut v_xs_2708_: *mut crate::leanh::LeanObject,
    mut v_sz_2709_: usize,
    mut v_i_2710_: usize,
    mut v_bs_2711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2712_: u8 = 0;
    let mut v_v_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: usize = 0;
    let mut v___x_2718_: usize = 0;
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2712_ = lean_usize_dec_lt(v_i_2710_, v_sz_2709_);
                if v___x_2712_ == 0 {
                    crate::leanh::lean_dec_ref(v_xs_2708_);
                    return v_bs_2711_;
                } else {
                    v_v_2713_ = lean_array_uget(v_bs_2711_, v_i_2710_);
                    v___x_2714_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2715_ = lean_array_uset(v_bs_2711_, v_i_2710_, v___x_2714_);
                    crate::leanh::lean_inc_ref(v_xs_2708_);
                    v___x_2716_ = l_Lean_Expr_beta(v_v_2713_, v_xs_2708_);
                    v___x_2717_ = 1usize;
                    v___x_2718_ = lean_usize_add(v_i_2710_, v___x_2717_);
                    v___x_2719_ = lean_array_uset(v_bs_x27_2715_, v_i_2710_, v___x_2716_);
                    v_i_2710_ = v___x_2718_;
                    v_bs_2711_ = v___x_2719_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1___boxed(
    mut v_xs_2721_: *mut crate::leanh::LeanObject,
    mut v_sz_2722_: *mut crate::leanh::LeanObject,
    mut v_i_2723_: *mut crate::leanh::LeanObject,
    mut v_bs_2724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2725_: usize = 0;
    let mut v_i_boxed_2726_: usize = 0;
    let mut v_res_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2725_ = crate::leanh::lean_unbox_usize(v_sz_2722_);
    crate::leanh::lean_dec(v_sz_2722_);
    v_i_boxed_2726_ = crate::leanh::lean_unbox_usize(v_i_2723_);
    crate::leanh::lean_dec(v_i_2723_);
    v_res_2727_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1(v_xs_2721_, v_sz_boxed_2725_, v_i_boxed_2726_, v_bs_2724_);
    return v_res_2727_;
}
pub unsafe fn _init_l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2730_ = l_Lean_Meta_PProdN_packLambdas___lam__0___closed__1;
    v___x_2731_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_2732_ = crate::leanh::lean_unsigned_to_nat(175);
    v___x_2733_ = l_Lean_Meta_PProdN_packLambdas___lam__0___closed__0;
    v___x_2734_ = l_Lean_Meta_mkPProdFst___closed__0;
    v___x_2735_ = l_mkPanicMessageWithDecl(
        v___x_2734_,
        v___x_2733_,
        v___x_2732_,
        v___x_2731_,
        v___x_2730_,
    );
    return v___x_2735_;
}
pub unsafe fn l_Lean_Meta_PProdN_packLambdas___lam__0(
    mut v_es_2736_: *mut crate::leanh::LeanObject,
    mut v___x_2737_: u8,
    mut v_xs_2738_: *mut crate::leanh::LeanObject,
    mut v_sort_2739_: *mut crate::leanh::LeanObject,
    mut v___y_2740_: *mut crate::leanh::LeanObject,
    mut v___y_2741_: *mut crate::leanh::LeanObject,
    mut v___y_2742_: *mut crate::leanh::LeanObject,
    mut v___y_2743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2745_: u8 = 0;
    v___x_2745_ = l_Lean_Expr_isSort(v_sort_2739_);
    if v___x_2745_ == 0 {
        let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_xs_2738_);
        crate::leanh::lean_dec_ref(v_es_2736_);
        v___x_2746_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2),
            core::ptr::addr_of_mut!(l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2_once),
            _init_l_Lean_Meta_PProdN_packLambdas___lam__0___closed__2,
        );
        v___x_2747_ = l_panic___at___00Lean_Meta_PProdN_packLambdas_spec__0(
            v___x_2746_,
            v___y_2740_,
            v___y_2741_,
            v___y_2742_,
            v___y_2743_,
        );
        return v___x_2747_;
    } else {
        let mut v_sz_2748_: usize = 0;
        let mut v___x_2749_: usize = 0;
        let mut v_es_x27_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_sz_2748_ = lean_array_size(v_es_2736_);
        v___x_2749_ = 0usize;
        crate::leanh::lean_inc_ref(v_xs_2738_);
        v_es_x27_2750_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1(v_xs_2738_, v_sz_2748_, v___x_2749_, v_es_2736_);
        v___x_2751_ = l_Lean_Expr_sortLevel_x21(v_sort_2739_);
        v___x_2752_ = l_Lean_Meta_PProdN_pack(
            v___x_2751_,
            v_es_x27_2750_,
            v___y_2740_,
            v___y_2741_,
            v___y_2742_,
            v___y_2743_,
        );
        if crate::leanh::lean_obj_tag(v___x_2752_) == 0 {
            let mut v_a_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2754_: u8 = 0;
            let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_2753_ = crate::leanh::lean_ctor_get(v___x_2752_, 0);
            crate::leanh::lean_inc(v_a_2753_);
            crate::leanh::lean_dec_ref_known(v___x_2752_, 1);
            v___x_2754_ = 1;
            v___x_2755_ = l_Lean_Meta_mkLambdaFVars(
                v_xs_2738_,
                v_a_2753_,
                v___x_2737_,
                v___x_2745_,
                v___x_2737_,
                v___x_2745_,
                v___x_2754_,
                v___y_2740_,
                v___y_2741_,
                v___y_2742_,
                v___y_2743_,
            );
            crate::leanh::lean_dec_ref(v_xs_2738_);
            return v___x_2755_;
        } else {
            crate::leanh::lean_dec_ref(v_xs_2738_);
            return v___x_2752_;
        }
    }
}
pub unsafe fn l_Lean_Meta_PProdN_packLambdas___lam__0___boxed(
    mut v_es_2756_: *mut crate::leanh::LeanObject,
    mut v___x_2757_: *mut crate::leanh::LeanObject,
    mut v_xs_2758_: *mut crate::leanh::LeanObject,
    mut v_sort_2759_: *mut crate::leanh::LeanObject,
    mut v___y_2760_: *mut crate::leanh::LeanObject,
    mut v___y_2761_: *mut crate::leanh::LeanObject,
    mut v___y_2762_: *mut crate::leanh::LeanObject,
    mut v___y_2763_: *mut crate::leanh::LeanObject,
    mut v___y_2764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1006__boxed_2765_: u8 = 0;
    let mut v_res_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1006__boxed_2765_ = (crate::leanh::lean_unbox(v___x_2757_) as u8);
    v_res_2766_ = l_Lean_Meta_PProdN_packLambdas___lam__0(
        v_es_2756_,
        v___x_1006__boxed_2765_,
        v_xs_2758_,
        v_sort_2759_,
        v___y_2760_,
        v___y_2761_,
        v___y_2762_,
        v___y_2763_,
    );
    crate::leanh::lean_dec(v___y_2763_);
    crate::leanh::lean_dec_ref(v___y_2762_);
    crate::leanh::lean_dec(v___y_2761_);
    crate::leanh::lean_dec_ref(v___y_2760_);
    crate::leanh::lean_dec_ref(v_sort_2759_);
    return v_res_2766_;
}
pub unsafe fn l_Lean_Meta_PProdN_packLambdas(
    mut v_type_2767_: *mut crate::leanh::LeanObject,
    mut v_es_2768_: *mut crate::leanh::LeanObject,
    mut v_a_2769_: *mut crate::leanh::LeanObject,
    mut v_a_2770_: *mut crate::leanh::LeanObject,
    mut v_a_2771_: *mut crate::leanh::LeanObject,
    mut v_a_2772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: u8 = 0;
    v___x_2774_ = lean_array_get_size(v_es_2768_);
    v___x_2775_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2776_ = lean_nat_dec_eq(v___x_2774_, v___x_2775_);
    if v___x_2776_ == 0 {
        let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2777_ = crate::leanh::lean_box((v___x_2776_) as usize);
        v___f_2778_ = crate::leanh::lean_alloc_closure(
            l_Lean_Meta_PProdN_packLambdas___lam__0___boxed as *mut core::ffi::c_void,
            9,
            2,
        );
        crate::leanh::lean_closure_set(v___f_2778_, 0, v_es_2768_);
        crate::leanh::lean_closure_set(v___f_2778_, 1, v___x_2777_);
        v___x_2779_ =
            l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(
                v_type_2767_,
                v___f_2778_,
                v___x_2776_,
                v_a_2769_,
                v_a_2770_,
                v_a_2771_,
                v_a_2772_,
            );
        return v___x_2779_;
    } else {
        let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_type_2767_);
        v___x_2780_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2781_ = lean_array_fget(v_es_2768_, v___x_2780_);
        crate::leanh::lean_dec_ref(v_es_2768_);
        v___x_2782_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2782_, 0, v___x_2781_);
        return v___x_2782_;
    }
}
pub unsafe fn l_Lean_Meta_PProdN_packLambdas___boxed(
    mut v_type_2783_: *mut crate::leanh::LeanObject,
    mut v_es_2784_: *mut crate::leanh::LeanObject,
    mut v_a_2785_: *mut crate::leanh::LeanObject,
    mut v_a_2786_: *mut crate::leanh::LeanObject,
    mut v_a_2787_: *mut crate::leanh::LeanObject,
    mut v_a_2788_: *mut crate::leanh::LeanObject,
    mut v_a_2789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2790_ = l_Lean_Meta_PProdN_packLambdas(
        v_type_2783_,
        v_es_2784_,
        v_a_2785_,
        v_a_2786_,
        v_a_2787_,
        v_a_2788_,
    );
    crate::leanh::lean_dec(v_a_2788_);
    crate::leanh::lean_dec_ref(v_a_2787_);
    crate::leanh::lean_dec(v_a_2786_);
    crate::leanh::lean_dec_ref(v_a_2785_);
    return v_res_2790_;
}
pub unsafe fn l_Lean_Meta_PProdN_mkLambdas___lam__0(
    mut v_es_2791_: *mut crate::leanh::LeanObject,
    mut v___x_2792_: u8,
    mut v_xs_2793_: *mut crate::leanh::LeanObject,
    mut v_body_2794_: *mut crate::leanh::LeanObject,
    mut v___y_2795_: *mut crate::leanh::LeanObject,
    mut v___y_2796_: *mut crate::leanh::LeanObject,
    mut v___y_2797_: *mut crate::leanh::LeanObject,
    mut v___y_2798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2802_: usize = 0;
    let mut v___x_2803_: usize = 0;
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: u8 = 0;
    let mut v___x_2808_: u8 = 0;
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2813_: u8 = 0;
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2817_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2800_ = l_Lean_Meta_getLevel(
                    v_body_2794_,
                    v___y_2795_,
                    v___y_2796_,
                    v___y_2797_,
                    v___y_2798_,
                );
                if crate::leanh::lean_obj_tag(v___x_2800_) == 0 {
                    v_a_2801_ = crate::leanh::lean_ctor_get(v___x_2800_, 0);
                    crate::leanh::lean_inc(v_a_2801_);
                    crate::leanh::lean_dec_ref_known(v___x_2800_, 1);
                    v_sz_2802_ = lean_array_size(v_es_2791_);
                    v___x_2803_ = 0usize;
                    crate::leanh::lean_inc_ref(v_xs_2793_);
                    v___x_2804_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_PProdN_packLambdas_spec__1(v_xs_2793_, v_sz_2802_, v___x_2803_, v_es_2791_);
                    v___x_2805_ = l_Lean_Meta_PProdN_mk(
                        v_a_2801_,
                        v___x_2804_,
                        v___y_2795_,
                        v___y_2796_,
                        v___y_2797_,
                        v___y_2798_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2805_) == 0 {
                        v_a_2806_ = crate::leanh::lean_ctor_get(v___x_2805_, 0);
                        crate::leanh::lean_inc(v_a_2806_);
                        crate::leanh::lean_dec_ref_known(v___x_2805_, 1);
                        v___x_2807_ = 1;
                        v___x_2808_ = 1;
                        v___x_2809_ = l_Lean_Meta_mkLambdaFVars(
                            v_xs_2793_,
                            v_a_2806_,
                            v___x_2792_,
                            v___x_2807_,
                            v___x_2792_,
                            v___x_2807_,
                            v___x_2808_,
                            v___y_2795_,
                            v___y_2796_,
                            v___y_2797_,
                            v___y_2798_,
                        );
                        crate::leanh::lean_dec_ref(v_xs_2793_);
                        return v___x_2809_;
                    } else {
                        crate::leanh::lean_dec_ref(v_xs_2793_);
                        return v___x_2805_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_xs_2793_);
                    crate::leanh::lean_dec_ref(v_es_2791_);
                    v_a_2810_ = crate::leanh::lean_ctor_get(v___x_2800_, 0);
                    v_isSharedCheck_2817_ = (!crate::leanh::lean_is_exclusive(v___x_2800_)) as u8;
                    if v_isSharedCheck_2817_ == 0 {
                        v___x_2812_ = v___x_2800_;
                        v_isShared_2813_ = v_isSharedCheck_2817_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2810_);
                        crate::leanh::lean_dec(v___x_2800_);
                        v___x_2812_ = crate::leanh::lean_box(0);
                        v_isShared_2813_ = v_isSharedCheck_2817_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2813_ == 0 {
                    v___x_2815_ = v___x_2812_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2816_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
                    v___x_2815_ = v_reuseFailAlloc_2816_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2815_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_PProdN_mkLambdas___lam__0___boxed(
    mut v_es_2818_: *mut crate::leanh::LeanObject,
    mut v___x_2819_: *mut crate::leanh::LeanObject,
    mut v_xs_2820_: *mut crate::leanh::LeanObject,
    mut v_body_2821_: *mut crate::leanh::LeanObject,
    mut v___y_2822_: *mut crate::leanh::LeanObject,
    mut v___y_2823_: *mut crate::leanh::LeanObject,
    mut v___y_2824_: *mut crate::leanh::LeanObject,
    mut v___y_2825_: *mut crate::leanh::LeanObject,
    mut v___y_2826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_371__boxed_2827_: u8 = 0;
    let mut v_res_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_371__boxed_2827_ = (crate::leanh::lean_unbox(v___x_2819_) as u8);
    v_res_2828_ = l_Lean_Meta_PProdN_mkLambdas___lam__0(
        v_es_2818_,
        v___x_371__boxed_2827_,
        v_xs_2820_,
        v_body_2821_,
        v___y_2822_,
        v___y_2823_,
        v___y_2824_,
        v___y_2825_,
    );
    crate::leanh::lean_dec(v___y_2825_);
    crate::leanh::lean_dec_ref(v___y_2824_);
    crate::leanh::lean_dec(v___y_2823_);
    crate::leanh::lean_dec_ref(v___y_2822_);
    return v_res_2828_;
}
pub unsafe fn l_Lean_Meta_PProdN_mkLambdas(
    mut v_type_2829_: *mut crate::leanh::LeanObject,
    mut v_es_2830_: *mut crate::leanh::LeanObject,
    mut v_a_2831_: *mut crate::leanh::LeanObject,
    mut v_a_2832_: *mut crate::leanh::LeanObject,
    mut v_a_2833_: *mut crate::leanh::LeanObject,
    mut v_a_2834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: u8 = 0;
    v___x_2836_ = lean_array_get_size(v_es_2830_);
    v___x_2837_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2838_ = lean_nat_dec_eq(v___x_2836_, v___x_2837_);
    if v___x_2838_ == 0 {
        let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2839_ = crate::leanh::lean_box((v___x_2838_) as usize);
        v___f_2840_ = crate::leanh::lean_alloc_closure(
            l_Lean_Meta_PProdN_mkLambdas___lam__0___boxed as *mut core::ffi::c_void,
            9,
            2,
        );
        crate::leanh::lean_closure_set(v___f_2840_, 0, v_es_2830_);
        crate::leanh::lean_closure_set(v___f_2840_, 1, v___x_2839_);
        v___x_2841_ =
            l_Lean_Meta_forallTelescope___at___00Lean_Meta_PProdN_packLambdas_spec__2___redArg(
                v_type_2829_,
                v___f_2840_,
                v___x_2838_,
                v_a_2831_,
                v_a_2832_,
                v_a_2833_,
                v_a_2834_,
            );
        return v___x_2841_;
    } else {
        let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_type_2829_);
        v___x_2842_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2843_ = lean_array_fget(v_es_2830_, v___x_2842_);
        crate::leanh::lean_dec_ref(v_es_2830_);
        v___x_2844_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2844_, 0, v___x_2843_);
        return v___x_2844_;
    }
}
pub unsafe fn l_Lean_Meta_PProdN_mkLambdas___boxed(
    mut v_type_2845_: *mut crate::leanh::LeanObject,
    mut v_es_2846_: *mut crate::leanh::LeanObject,
    mut v_a_2847_: *mut crate::leanh::LeanObject,
    mut v_a_2848_: *mut crate::leanh::LeanObject,
    mut v_a_2849_: *mut crate::leanh::LeanObject,
    mut v_a_2850_: *mut crate::leanh::LeanObject,
    mut v_a_2851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2852_ = l_Lean_Meta_PProdN_mkLambdas(
        v_type_2845_,
        v_es_2846_,
        v_a_2847_,
        v_a_2848_,
        v_a_2849_,
        v_a_2850_,
    );
    crate::leanh::lean_dec(v_a_2850_);
    crate::leanh::lean_dec_ref(v_a_2849_);
    crate::leanh::lean_dec(v_a_2848_);
    crate::leanh::lean_dec_ref(v_a_2847_);
    return v_res_2852_;
}
pub unsafe fn l_Lean_Meta_PProdN_stripProjs(
    mut v_e_2853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_typeName_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: u8 = 0;
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_2853_) == 11 {
                    v_typeName_2854_ = crate::leanh::lean_ctor_get(v_e_2853_, 0);
                    if crate::leanh::lean_obj_tag(v_typeName_2854_) == 1 {
                        v_pre_2855_ = crate::leanh::lean_ctor_get(v_typeName_2854_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_2855_) == 0 {
                            v_struct_2856_ = crate::leanh::lean_ctor_get(v_e_2853_, 2);
                            v_str_2857_ = crate::leanh::lean_ctor_get(v_typeName_2854_, 1);
                            v___x_2858_ = l_Lean_Meta_mkPProd___closed__0;
                            v___x_2859_ = lean_string_dec_eq(v_str_2857_, v___x_2858_);
                            if v___x_2859_ == 0 {
                                v___x_2860_ = l_Lean_Meta_mkPProd___closed__2;
                                v___x_2861_ = lean_string_dec_eq(v_str_2857_, v___x_2860_);
                                if v___x_2861_ == 0 {
                                    crate::leanh::lean_inc_ref(v_e_2853_);
                                    return v_e_2853_;
                                } else {
                                    v_e_2853_ = v_struct_2856_;
                                    state = 0;
                                    continue;
                                }
                            } else {
                                v_e_2853_ = v_struct_2856_;
                                state = 0;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_inc_ref(v_e_2853_);
                            return v_e_2853_;
                        }
                    } else {
                        crate::leanh::lean_inc_ref(v_e_2853_);
                        return v_e_2853_;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_e_2853_);
                    return v_e_2853_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_PProdN_stripProjs___boxed(
    mut v_e_2864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2865_ = l_Lean_Meta_PProdN_stripProjs(v_e_2864_);
    crate::leanh::lean_dec_ref(v_e_2864_);
    return v_res_2865_;
}
pub unsafe fn l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(
    mut v_e_2868_: *mut crate::leanh::LeanObject,
    mut v_i_2869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2872_: u8 = 0;
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: u8 = 0;
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: u8 = 0;
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2886_ = l_Lean_Meta_mkPProdMk___closed__1;
                v___x_2887_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2888_ = l_Lean_Expr_isAppOfArity(v_e_2868_, v___x_2886_, v___x_2887_);
                if v___x_2888_ == 0 {
                    v___x_2889_ = l_Lean_Meta_mkPProdMk___closed__3;
                    v___x_2890_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_2891_ = l_Lean_Expr_isAppOfArity(v_e_2868_, v___x_2889_, v___x_2890_);
                    v___y_2872_ = v___x_2891_;
                    state = 1;
                    continue;
                } else {
                    v___y_2872_ = v___x_2888_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_2872_ == 0 {
                    v___x_2873_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___closed__0;
                    v___x_2874_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2874_, 0, v___x_2873_);
                    return v___x_2874_;
                } else {
                    v___x_2875_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2876_ = lean_nat_dec_eq(v_i_2869_, v___x_2875_);
                    if v___x_2876_ == 0 {
                        v___x_2877_ = l_Lean_Expr_appArg_x21(v_e_2868_);
                        v___x_2878_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2878_, 0, v___x_2877_);
                        v___x_2879_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2879_, 0, v___x_2878_);
                        v___x_2880_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2880_, 0, v___x_2879_);
                        return v___x_2880_;
                    } else {
                        v___x_2881_ = l_Lean_Expr_appFn_x21(v_e_2868_);
                        v___x_2882_ = l_Lean_Expr_appArg_x21(v___x_2881_);
                        crate::leanh::lean_dec_ref(v___x_2881_);
                        v___x_2883_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2883_, 0, v___x_2882_);
                        v___x_2884_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2884_, 0, v___x_2883_);
                        v___x_2885_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2885_, 0, v___x_2884_);
                        return v___x_2885_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___boxed(
    mut v_e_2892_: *mut crate::leanh::LeanObject,
    mut v_i_2893_: *mut crate::leanh::LeanObject,
    mut v_a_2894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2895_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(
        v_e_2892_, v_i_2893_,
    );
    crate::leanh::lean_dec(v_i_2893_);
    crate::leanh::lean_dec_ref(v_e_2892_);
    return v_res_2895_;
}
pub unsafe fn l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce(
    mut v_e_2896_: *mut crate::leanh::LeanObject,
    mut v_i_2897_: *mut crate::leanh::LeanObject,
    mut v_a_2898_: *mut crate::leanh::LeanObject,
    mut v_a_2899_: *mut crate::leanh::LeanObject,
    mut v_a_2900_: *mut crate::leanh::LeanObject,
    mut v_a_2901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2903_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(
        v_e_2896_, v_i_2897_,
    );
    return v___x_2903_;
}
pub unsafe fn l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___boxed(
    mut v_e_2904_: *mut crate::leanh::LeanObject,
    mut v_i_2905_: *mut crate::leanh::LeanObject,
    mut v_a_2906_: *mut crate::leanh::LeanObject,
    mut v_a_2907_: *mut crate::leanh::LeanObject,
    mut v_a_2908_: *mut crate::leanh::LeanObject,
    mut v_a_2909_: *mut crate::leanh::LeanObject,
    mut v_a_2910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2911_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce(
        v_e_2904_, v_i_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_,
    );
    crate::leanh::lean_dec(v_a_2909_);
    crate::leanh::lean_dec_ref(v_a_2908_);
    crate::leanh::lean_dec(v_a_2907_);
    crate::leanh::lean_dec_ref(v_a_2906_);
    crate::leanh::lean_dec(v_i_2905_);
    crate::leanh::lean_dec_ref(v_e_2904_);
    return v_res_2911_;
}
pub unsafe fn l_Lean_Meta_PProdN_reduceProjs___lam__0(
    mut v_x_2912_: *mut crate::leanh::LeanObject,
    mut v___y_2913_: *mut crate::leanh::LeanObject,
    mut v___y_2914_: *mut crate::leanh::LeanObject,
    mut v___y_2915_: *mut crate::leanh::LeanObject,
    mut v___y_2916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2918_ =
        l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___closed__0;
    v___x_2919_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2919_, 0, v___x_2918_);
    return v___x_2919_;
}
pub unsafe fn l_Lean_Meta_PProdN_reduceProjs___lam__0___boxed(
    mut v_x_2920_: *mut crate::leanh::LeanObject,
    mut v___y_2921_: *mut crate::leanh::LeanObject,
    mut v___y_2922_: *mut crate::leanh::LeanObject,
    mut v___y_2923_: *mut crate::leanh::LeanObject,
    mut v___y_2924_: *mut crate::leanh::LeanObject,
    mut v___y_2925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2926_ = l_Lean_Meta_PProdN_reduceProjs___lam__0(
        v_x_2920_,
        v___y_2921_,
        v___y_2922_,
        v___y_2923_,
        v___y_2924_,
    );
    crate::leanh::lean_dec(v___y_2924_);
    crate::leanh::lean_dec_ref(v___y_2923_);
    crate::leanh::lean_dec(v___y_2922_);
    crate::leanh::lean_dec_ref(v___y_2921_);
    crate::leanh::lean_dec_ref(v_x_2920_);
    return v_res_2926_;
}
pub unsafe fn l_Lean_Meta_PProdN_reduceProjs___lam__1(
    mut v_e_2943_: *mut crate::leanh::LeanObject,
    mut v___y_2944_: *mut crate::leanh::LeanObject,
    mut v___y_2945_: *mut crate::leanh::LeanObject,
    mut v___y_2946_: *mut crate::leanh::LeanObject,
    mut v___y_2947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_e_x27_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2961_: u8 = 0;
    let mut v___x_2963_: u8 = 0;
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: u8 = 0;
    let mut v_arg_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: u8 = 0;
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: u8 = 0;
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: u8 = 0;
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: u8 = 0;
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: u8 = 0;
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: u8 = 0;
    let mut v_isSharedCheck_2987_: u8 = 0;
    let mut v_a_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2991_: u8 = 0;
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2995_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_2943_);
                v___x_2957_ =
                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2943_, v___y_2945_);
                if crate::leanh::lean_obj_tag(v___x_2957_) == 0 {
                    v_a_2958_ = crate::leanh::lean_ctor_get(v___x_2957_, 0);
                    v_isSharedCheck_2987_ = (!crate::leanh::lean_is_exclusive(v___x_2957_)) as u8;
                    if v_isSharedCheck_2987_ == 0 {
                        v___x_2960_ = v___x_2957_;
                        v_isShared_2961_ = v_isSharedCheck_2987_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2958_);
                        crate::leanh::lean_dec(v___x_2957_);
                        v___x_2960_ = crate::leanh::lean_box(0);
                        v_isShared_2961_ = v_isSharedCheck_2987_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2943_);
                    v_a_2988_ = crate::leanh::lean_ctor_get(v___x_2957_, 0);
                    v_isSharedCheck_2995_ = (!crate::leanh::lean_is_exclusive(v___x_2957_)) as u8;
                    if v_isSharedCheck_2995_ == 0 {
                        v___x_2990_ = v___x_2957_;
                        v_isShared_2991_ = v_isSharedCheck_2995_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2988_);
                        crate::leanh::lean_dec(v___x_2957_);
                        v___x_2990_ = crate::leanh::lean_box(0);
                        v_isShared_2991_ = v_isSharedCheck_2995_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2951_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2952_ =
                    l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(
                        v_e_x27_2950_,
                        v___x_2951_,
                    );
                crate::leanh::lean_dec_ref(v_e_x27_2950_);
                return v___x_2952_;
            }
            2 => {
                v___x_2955_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2956_ =
                    l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(
                        v_e_x27_2954_,
                        v___x_2955_,
                    );
                crate::leanh::lean_dec_ref(v_e_x27_2954_);
                return v___x_2956_;
            }
            3 => {
                v___x_2971_ = l_Lean_Expr_cleanupAnnotations(v_a_2958_);
                v___x_2972_ = l_Lean_Expr_isApp(v___x_2971_);
                if v___x_2972_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2971_);
                    state = 4;
                    continue;
                } else {
                    v_arg_2973_ = crate::leanh::lean_ctor_get(v___x_2971_, 1);
                    crate::leanh::lean_inc_ref(v_arg_2973_);
                    v___x_2974_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2971_);
                    v___x_2975_ = l_Lean_Expr_isApp(v___x_2974_);
                    if v___x_2975_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2974_);
                        crate::leanh::lean_dec_ref(v_arg_2973_);
                        state = 4;
                        continue;
                    } else {
                        v___x_2976_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2974_);
                        v___x_2977_ = l_Lean_Expr_isApp(v___x_2976_);
                        if v___x_2977_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2976_);
                            crate::leanh::lean_dec_ref(v_arg_2973_);
                            state = 4;
                            continue;
                        } else {
                            v___x_2978_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2976_);
                            v___x_2979_ = l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__1;
                            v___x_2980_ = l_Lean_Expr_isConstOf(v___x_2978_, v___x_2979_);
                            if v___x_2980_ == 0 {
                                v___x_2981_ = l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__3;
                                v___x_2982_ = l_Lean_Expr_isConstOf(v___x_2978_, v___x_2981_);
                                if v___x_2982_ == 0 {
                                    v___x_2983_ =
                                        l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__5;
                                    v___x_2984_ = l_Lean_Expr_isConstOf(v___x_2978_, v___x_2983_);
                                    if v___x_2984_ == 0 {
                                        v___x_2985_ =
                                            l_Lean_Meta_PProdN_reduceProjs___lam__1___closed__7;
                                        v___x_2986_ =
                                            l_Lean_Expr_isConstOf(v___x_2978_, v___x_2985_);
                                        crate::leanh::lean_dec_ref(v___x_2978_);
                                        if v___x_2986_ == 0 {
                                            crate::leanh::lean_dec_ref(v_arg_2973_);
                                            state = 4;
                                            continue;
                                        } else {
                                            crate::leanh::lean_del_object(v___x_2960_);
                                            crate::leanh::lean_dec_ref(v_e_2943_);
                                            v_e_x27_2950_ = v_arg_2973_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___x_2978_);
                                        crate::leanh::lean_del_object(v___x_2960_);
                                        crate::leanh::lean_dec_ref(v_e_2943_);
                                        v_e_x27_2950_ = v_arg_2973_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_2978_);
                                    crate::leanh::lean_del_object(v___x_2960_);
                                    crate::leanh::lean_dec_ref(v_e_2943_);
                                    v_e_x27_2954_ = v_arg_2973_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_2978_);
                                crate::leanh::lean_del_object(v___x_2960_);
                                crate::leanh::lean_dec_ref(v_e_2943_);
                                v_e_x27_2954_ = v_arg_2973_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            4 => {
                v___x_2963_ = l_Lean_Expr_isProj(v_e_2943_);
                if v___x_2963_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_2943_);
                    v___x_2964_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg___closed__0;
                    if v_isShared_2961_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2960_, 0, v___x_2964_);
                        v___x_2966_ = v___x_2960_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2967_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2964_);
                        v___x_2966_ = v_reuseFailAlloc_2967_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2960_);
                    v___x_2968_ = l_Lean_Expr_projExpr_x21(v_e_2943_);
                    v___x_2969_ = l_Lean_Expr_projIdx_x21(v_e_2943_);
                    crate::leanh::lean_dec_ref(v_e_2943_);
                    v___x_2970_ = l___private_Lean_Meta_PProdN_0__Lean_Meta_PProdN_reduceProjs_reduce___redArg(v___x_2968_, v___x_2969_);
                    crate::leanh::lean_dec(v___x_2969_);
                    crate::leanh::lean_dec_ref(v___x_2968_);
                    return v___x_2970_;
                }
            }
            5 => {
                return v___x_2966_;
            }
            6 => {
                if v_isShared_2991_ == 0 {
                    v___x_2993_ = v___x_2990_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2994_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_a_2988_);
                    v___x_2993_ = v_reuseFailAlloc_2994_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2993_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_PProdN_reduceProjs___lam__1___boxed(
    mut v_e_2996_: *mut crate::leanh::LeanObject,
    mut v___y_2997_: *mut crate::leanh::LeanObject,
    mut v___y_2998_: *mut crate::leanh::LeanObject,
    mut v___y_2999_: *mut crate::leanh::LeanObject,
    mut v___y_3000_: *mut crate::leanh::LeanObject,
    mut v___y_3001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3002_ = l_Lean_Meta_PProdN_reduceProjs___lam__1(
        v_e_2996_,
        v___y_2997_,
        v___y_2998_,
        v___y_2999_,
        v___y_3000_,
    );
    crate::leanh::lean_dec(v___y_3000_);
    crate::leanh::lean_dec_ref(v___y_2999_);
    crate::leanh::lean_dec(v___y_2998_);
    crate::leanh::lean_dec_ref(v___y_2997_);
    return v_res_3002_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg(
    mut v_a_3003_: *mut crate::leanh::LeanObject,
    mut v_x_3004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: u8 = 0;
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3004_) == 0 {
                    v___x_3005_ = crate::leanh::lean_box(0);
                    return v___x_3005_;
                } else {
                    v_key_3006_ = crate::leanh::lean_ctor_get(v_x_3004_, 0);
                    v_value_3007_ = crate::leanh::lean_ctor_get(v_x_3004_, 1);
                    v_tail_3008_ = crate::leanh::lean_ctor_get(v_x_3004_, 2);
                    v___x_3009_ = l_Lean_ExprStructEq_beq(v_key_3006_, v_a_3003_);
                    if v___x_3009_ == 0 {
                        v_x_3004_ = v_tail_3008_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_3007_);
                        v___x_3011_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3011_, 0, v_value_3007_);
                        return v___x_3011_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg___boxed(
    mut v_a_3012_: *mut crate::leanh::LeanObject,
    mut v_x_3013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3014_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg(v_a_3012_, v_x_3013_);
    crate::leanh::lean_dec(v_x_3013_);
    crate::leanh::lean_dec_ref(v_a_3012_);
    return v_res_3014_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg(
    mut v_m_3015_: *mut crate::leanh::LeanObject,
    mut v_a_3016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: u64 = 0;
    let mut v___x_3020_: u64 = 0;
    let mut v___x_3021_: u64 = 0;
    let mut v_fold_3022_: u64 = 0;
    let mut v___x_3023_: u64 = 0;
    let mut v___x_3024_: u64 = 0;
    let mut v___x_3025_: u64 = 0;
    let mut v___x_3026_: usize = 0;
    let mut v___x_3027_: usize = 0;
    let mut v___x_3028_: usize = 0;
    let mut v___x_3029_: usize = 0;
    let mut v___x_3030_: usize = 0;
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3017_ = crate::leanh::lean_ctor_get(v_m_3015_, 1);
    v___x_3018_ = lean_array_get_size(v_buckets_3017_);
    v___x_3019_ = l_Lean_ExprStructEq_hash(v_a_3016_);
    v___x_3020_ = 32u64;
    v___x_3021_ = lean_uint64_shift_right(v___x_3019_, v___x_3020_);
    v_fold_3022_ = lean_uint64_xor(v___x_3019_, v___x_3021_);
    v___x_3023_ = 16u64;
    v___x_3024_ = lean_uint64_shift_right(v_fold_3022_, v___x_3023_);
    v___x_3025_ = lean_uint64_xor(v_fold_3022_, v___x_3024_);
    v___x_3026_ = lean_uint64_to_usize(v___x_3025_);
    v___x_3027_ = lean_usize_of_nat(v___x_3018_);
    v___x_3028_ = 1usize;
    v___x_3029_ = lean_usize_sub(v___x_3027_, v___x_3028_);
    v___x_3030_ = lean_usize_land(v___x_3026_, v___x_3029_);
    v___x_3031_ = lean_array_uget_borrowed(v_buckets_3017_, v___x_3030_);
    v___x_3032_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg(v_a_3016_, v___x_3031_);
    return v___x_3032_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_m_3033_: *mut crate::leanh::LeanObject,
    mut v_a_3034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3035_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg(v_m_3033_, v_a_3034_);
    crate::leanh::lean_dec_ref(v_a_3034_);
    crate::leanh::lean_dec_ref(v_m_3033_);
    return v_res_3035_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__12___redArg(
    mut v_a_3036_: *mut crate::leanh::LeanObject,
    mut v_b_3037_: *mut crate::leanh::LeanObject,
    mut v_x_3038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3044_: u8 = 0;
    let mut v___x_3045_: u8 = 0;
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3053_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3038_) == 0 {
                    crate::leanh::lean_dec(v_b_3037_);
                    crate::leanh::lean_dec_ref(v_a_3036_);
                    return v_x_3038_;
                } else {
                    v_key_3039_ = crate::leanh::lean_ctor_get(v_x_3038_, 0);
                    v_value_3040_ = crate::leanh::lean_ctor_get(v_x_3038_, 1);
                    v_tail_3041_ = crate::leanh::lean_ctor_get(v_x_3038_, 2);
                    v_isSharedCheck_3053_ = (!crate::leanh::lean_is_exclusive(v_x_3038_)) as u8;
                    if v_isSharedCheck_3053_ == 0 {
                        v___x_3043_ = v_x_3038_;
                        v_isShared_3044_ = v_isSharedCheck_3053_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3041_);
                        crate::leanh::lean_inc(v_value_3040_);
                        crate::leanh::lean_inc(v_key_3039_);
                        crate::leanh::lean_dec(v_x_3038_);
                        v___x_3043_ = crate::leanh::lean_box(0);
                        v_isShared_3044_ = v_isSharedCheck_3053_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3045_ = l_Lean_ExprStructEq_beq(v_key_3039_, v_a_3036_);
                if v___x_3045_ == 0 {
                    v___x_3046_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__12___redArg(v_a_3036_, v_b_3037_, v_tail_3041_);
                    if v_isShared_3044_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3043_, 2, v___x_3046_);
                        v___x_3048_ = v___x_3043_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3049_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_key_3039_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3049_, 1, v_value_3040_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3049_, 2, v___x_3046_);
                        v___x_3048_ = v_reuseFailAlloc_3049_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_3040_);
                    crate::leanh::lean_dec(v_key_3039_);
                    if v_isShared_3044_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3043_, 1, v_b_3037_);
                        crate::leanh::lean_ctor_set(v___x_3043_, 0, v_a_3036_);
                        v___x_3051_ = v___x_3043_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3052_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_a_3036_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3052_, 1, v_b_3037_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3052_, 2, v_tail_3041_);
                        v___x_3051_ = v_reuseFailAlloc_3052_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3048_;
            }
            3 => {
                return v___x_3051_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(
    mut v_x_3054_: *mut crate::leanh::LeanObject,
    mut v_x_3055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3061_: u8 = 0;
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: u64 = 0;
    let mut v___x_3064_: u64 = 0;
    let mut v___x_3065_: u64 = 0;
    let mut v_fold_3066_: u64 = 0;
    let mut v___x_3067_: u64 = 0;
    let mut v___x_3068_: u64 = 0;
    let mut v___x_3069_: u64 = 0;
    let mut v___x_3070_: usize = 0;
    let mut v___x_3071_: usize = 0;
    let mut v___x_3072_: usize = 0;
    let mut v___x_3073_: usize = 0;
    let mut v___x_3074_: usize = 0;
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3081_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3055_) == 0 {
                    return v_x_3054_;
                } else {
                    v_key_3056_ = crate::leanh::lean_ctor_get(v_x_3055_, 0);
                    v_value_3057_ = crate::leanh::lean_ctor_get(v_x_3055_, 1);
                    v_tail_3058_ = crate::leanh::lean_ctor_get(v_x_3055_, 2);
                    v_isSharedCheck_3081_ = (!crate::leanh::lean_is_exclusive(v_x_3055_)) as u8;
                    if v_isSharedCheck_3081_ == 0 {
                        v___x_3060_ = v_x_3055_;
                        v_isShared_3061_ = v_isSharedCheck_3081_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3058_);
                        crate::leanh::lean_inc(v_value_3057_);
                        crate::leanh::lean_inc(v_key_3056_);
                        crate::leanh::lean_dec(v_x_3055_);
                        v___x_3060_ = crate::leanh::lean_box(0);
                        v_isShared_3061_ = v_isSharedCheck_3081_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3062_ = lean_array_get_size(v_x_3054_);
                v___x_3063_ = l_Lean_ExprStructEq_hash(v_key_3056_);
                v___x_3064_ = 32u64;
                v___x_3065_ = lean_uint64_shift_right(v___x_3063_, v___x_3064_);
                v_fold_3066_ = lean_uint64_xor(v___x_3063_, v___x_3065_);
                v___x_3067_ = 16u64;
                v___x_3068_ = lean_uint64_shift_right(v_fold_3066_, v___x_3067_);
                v___x_3069_ = lean_uint64_xor(v_fold_3066_, v___x_3068_);
                v___x_3070_ = lean_uint64_to_usize(v___x_3069_);
                v___x_3071_ = lean_usize_of_nat(v___x_3062_);
                v___x_3072_ = 1usize;
                v___x_3073_ = lean_usize_sub(v___x_3071_, v___x_3072_);
                v___x_3074_ = lean_usize_land(v___x_3070_, v___x_3073_);
                v___x_3075_ = lean_array_uget_borrowed(v_x_3054_, v___x_3074_);
                crate::leanh::lean_inc(v___x_3075_);
                if v_isShared_3061_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3060_, 2, v___x_3075_);
                    v___x_3077_ = v___x_3060_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3080_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_key_3056_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3080_, 1, v_value_3057_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3080_, 2, v___x_3075_);
                    v___x_3077_ = v_reuseFailAlloc_3080_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3078_ = lean_array_uset(v_x_3054_, v___x_3074_, v___x_3077_);
                v_x_3054_ = v___x_3078_;
                v_x_3055_ = v_tail_3058_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(
    mut v_i_3082_: *mut crate::leanh::LeanObject,
    mut v_source_3083_: *mut crate::leanh::LeanObject,
    mut v_target_3084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: u8 = 0;
    let mut v_es_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3085_ = lean_array_get_size(v_source_3083_);
                v___x_3086_ = lean_nat_dec_lt(v_i_3082_, v___x_3085_);
                if v___x_3086_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_3083_);
                    crate::leanh::lean_dec(v_i_3082_);
                    return v_target_3084_;
                } else {
                    v_es_3087_ = lean_array_fget(v_source_3083_, v_i_3082_);
                    v___x_3088_ = crate::leanh::lean_box(0);
                    v_source_3089_ = lean_array_fset(v_source_3083_, v_i_3082_, v___x_3088_);
                    v_target_3090_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_3084_, v_es_3087_);
                    v___x_3091_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3092_ = lean_nat_add(v_i_3082_, v___x_3091_);
                    crate::leanh::lean_dec(v_i_3082_);
                    v_i_3082_ = v___x_3092_;
                    v_source_3083_ = v_source_3089_;
                    v_target_3084_ = v_target_3090_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11___redArg(
    mut v_data_3094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3095_ = lean_array_get_size(v_data_3094_);
    v___x_3096_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3097_ = lean_nat_mul(v___x_3095_, v___x_3096_);
    v___x_3098_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3099_ = crate::leanh::lean_box(0);
    v___x_3100_ = lean_mk_array(v_nbuckets_3097_, v___x_3099_);
    v___x_3101_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_3098_, v_data_3094_, v___x_3100_);
    return v___x_3101_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg(
    mut v_a_3102_: *mut crate::leanh::LeanObject,
    mut v_x_3103_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3104_: u8 = 0;
    let mut v_key_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3103_) == 0 {
                    v___x_3104_ = 0;
                    return v___x_3104_;
                } else {
                    v_key_3105_ = crate::leanh::lean_ctor_get(v_x_3103_, 0);
                    v_tail_3106_ = crate::leanh::lean_ctor_get(v_x_3103_, 2);
                    v___x_3107_ = l_Lean_ExprStructEq_beq(v_key_3105_, v_a_3102_);
                    if v___x_3107_ == 0 {
                        v_x_3103_ = v_tail_3106_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3107_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg___boxed(
    mut v_a_3109_: *mut crate::leanh::LeanObject,
    mut v_x_3110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3111_: u8 = 0;
    let mut v_r_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3111_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg(v_a_3109_, v_x_3110_);
    crate::leanh::lean_dec(v_x_3110_);
    crate::leanh::lean_dec_ref(v_a_3109_);
    v_r_3112_ = crate::leanh::lean_box((v_res_3111_) as usize);
    return v_r_3112_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6___redArg(
    mut v_m_3113_: *mut crate::leanh::LeanObject,
    mut v_a_3114_: *mut crate::leanh::LeanObject,
    mut v_b_3115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3120_: u8 = 0;
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: u64 = 0;
    let mut v___x_3123_: u64 = 0;
    let mut v___x_3124_: u64 = 0;
    let mut v_fold_3125_: u64 = 0;
    let mut v___x_3126_: u64 = 0;
    let mut v___x_3127_: u64 = 0;
    let mut v___x_3128_: u64 = 0;
    let mut v___x_3129_: usize = 0;
    let mut v___x_3130_: usize = 0;
    let mut v___x_3131_: usize = 0;
    let mut v___x_3132_: usize = 0;
    let mut v___x_3133_: usize = 0;
    let mut v_bkt_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: u8 = 0;
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: u8 = 0;
    let mut v_val_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3160_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3116_ = crate::leanh::lean_ctor_get(v_m_3113_, 0);
                v_buckets_3117_ = crate::leanh::lean_ctor_get(v_m_3113_, 1);
                v_isSharedCheck_3160_ = (!crate::leanh::lean_is_exclusive(v_m_3113_)) as u8;
                if v_isSharedCheck_3160_ == 0 {
                    v___x_3119_ = v_m_3113_;
                    v_isShared_3120_ = v_isSharedCheck_3160_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_3117_);
                    crate::leanh::lean_inc(v_size_3116_);
                    crate::leanh::lean_dec(v_m_3113_);
                    v___x_3119_ = crate::leanh::lean_box(0);
                    v_isShared_3120_ = v_isSharedCheck_3160_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3121_ = lean_array_get_size(v_buckets_3117_);
                v___x_3122_ = l_Lean_ExprStructEq_hash(v_a_3114_);
                v___x_3123_ = 32u64;
                v___x_3124_ = lean_uint64_shift_right(v___x_3122_, v___x_3123_);
                v_fold_3125_ = lean_uint64_xor(v___x_3122_, v___x_3124_);
                v___x_3126_ = 16u64;
                v___x_3127_ = lean_uint64_shift_right(v_fold_3125_, v___x_3126_);
                v___x_3128_ = lean_uint64_xor(v_fold_3125_, v___x_3127_);
                v___x_3129_ = lean_uint64_to_usize(v___x_3128_);
                v___x_3130_ = lean_usize_of_nat(v___x_3121_);
                v___x_3131_ = 1usize;
                v___x_3132_ = lean_usize_sub(v___x_3130_, v___x_3131_);
                v___x_3133_ = lean_usize_land(v___x_3129_, v___x_3132_);
                v_bkt_3134_ = lean_array_uget_borrowed(v_buckets_3117_, v___x_3133_);
                v___x_3135_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg(v_a_3114_, v_bkt_3134_);
                if v___x_3135_ == 0 {
                    v___x_3136_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3137_ = lean_nat_add(v_size_3116_, v___x_3136_);
                    crate::leanh::lean_dec(v_size_3116_);
                    crate::leanh::lean_inc(v_bkt_3134_);
                    v___x_3138_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3138_, 0, v_a_3114_);
                    crate::leanh::lean_ctor_set(v___x_3138_, 1, v_b_3115_);
                    crate::leanh::lean_ctor_set(v___x_3138_, 2, v_bkt_3134_);
                    v_buckets_x27_3139_ =
                        lean_array_uset(v_buckets_3117_, v___x_3133_, v___x_3138_);
                    v___x_3140_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3141_ = lean_nat_mul(v_size_x27_3137_, v___x_3140_);
                    v___x_3142_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_3143_ = lean_nat_div(v___x_3141_, v___x_3142_);
                    crate::leanh::lean_dec(v___x_3141_);
                    v___x_3144_ = lean_array_get_size(v_buckets_x27_3139_);
                    v___x_3145_ = lean_nat_dec_le(v___x_3143_, v___x_3144_);
                    crate::leanh::lean_dec(v___x_3143_);
                    if v___x_3145_ == 0 {
                        v_val_3146_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_3139_);
                        if v_isShared_3120_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3119_, 1, v_val_3146_);
                            crate::leanh::lean_ctor_set(v___x_3119_, 0, v_size_x27_3137_);
                            v___x_3148_ = v___x_3119_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3149_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3149_,
                                0,
                                v_size_x27_3137_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3149_, 1, v_val_3146_);
                            v___x_3148_ = v_reuseFailAlloc_3149_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3120_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3119_, 1, v_buckets_x27_3139_);
                            crate::leanh::lean_ctor_set(v___x_3119_, 0, v_size_x27_3137_);
                            v___x_3151_ = v___x_3119_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3152_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3152_,
                                0,
                                v_size_x27_3137_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3152_,
                                1,
                                v_buckets_x27_3139_,
                            );
                            v___x_3151_ = v_reuseFailAlloc_3152_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_3134_);
                    v___x_3153_ = crate::leanh::lean_box(0);
                    v_buckets_x27_3154_ =
                        lean_array_uset(v_buckets_3117_, v___x_3133_, v___x_3153_);
                    v___x_3155_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__12___redArg(v_a_3114_, v_b_3115_, v_bkt_3134_);
                    v___x_3156_ = lean_array_uset(v_buckets_x27_3154_, v___x_3133_, v___x_3155_);
                    if v_isShared_3120_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3119_, 1, v___x_3156_);
                        v___x_3158_ = v___x_3119_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3159_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_size_3116_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3159_, 1, v___x_3156_);
                        v___x_3158_ = v_reuseFailAlloc_3159_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3148_;
            }
            3 => {
                return v___x_3151_;
            }
            4 => {
                return v___x_3158_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__2(
    mut v_a_3161_: *mut crate::leanh::LeanObject,
    mut v_e_3162_: *mut crate::leanh::LeanObject,
    mut v_a_3163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3165_ = lean_st_ref_take(v_a_3161_);
    v___x_3166_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6___redArg(v___x_3165_, v_e_3162_, v_a_3163_);
    v___x_3167_ = lean_st_ref_set(v_a_3161_, v___x_3166_);
    v___x_3168_ = crate::leanh::lean_box(0);
    return v___x_3168_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__2___boxed(
    mut v_a_3169_: *mut crate::leanh::LeanObject,
    mut v_e_3170_: *mut crate::leanh::LeanObject,
    mut v_a_3171_: *mut crate::leanh::LeanObject,
    mut v___y_3172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3173_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__2(v_a_3169_, v_e_3170_, v_a_3171_);
    crate::leanh::lean_dec(v_a_3169_);
    return v_res_3173_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0(
    mut v_00_u03b1_3174_: *mut crate::leanh::LeanObject,
    mut v_x_3175_: *mut crate::leanh::LeanObject,
    mut v___y_3176_: *mut crate::leanh::LeanObject,
    mut v___y_3177_: *mut crate::leanh::LeanObject,
    mut v___y_3178_: *mut crate::leanh::LeanObject,
    mut v___y_3179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3181_ = crate::leanh::lean_apply_1(v_x_3175_, crate::leanh::lean_box(0));
    v___x_3182_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3182_, 0, v___x_3181_);
    return v___x_3182_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0___boxed(
    mut v_00_u03b1_3183_: *mut crate::leanh::LeanObject,
    mut v_x_3184_: *mut crate::leanh::LeanObject,
    mut v___y_3185_: *mut crate::leanh::LeanObject,
    mut v___y_3186_: *mut crate::leanh::LeanObject,
    mut v___y_3187_: *mut crate::leanh::LeanObject,
    mut v___y_3188_: *mut crate::leanh::LeanObject,
    mut v___y_3189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3190_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0(v_00_u03b1_3183_, v_x_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
    crate::leanh::lean_dec(v___y_3188_);
    crate::leanh::lean_dec_ref(v___y_3187_);
    crate::leanh::lean_dec(v___y_3186_);
    crate::leanh::lean_dec_ref(v___y_3185_);
    return v_res_3190_;
}
pub unsafe fn _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3191_ = crate::leanh::lean_box(0);
    v___x_3192_ = l_Lean_interruptExceptionId;
    v___x_3193_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3193_, 0, v___x_3192_);
    crate::leanh::lean_ctor_set(v___x_3193_, 1, v___x_3191_);
    return v___x_3193_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3195_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once), _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
    v___x_3196_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3196_, 0, v___x_3195_);
    return v___x_3196_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg___boxed(
    mut v___y_3197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3198_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg();
    return v_res_3198_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3204_ = l_Lean_maxRecDepthErrorMessage;
    v___x_3205_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3205_, 0, v___x_3204_);
    return v___x_3205_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3206_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
    v___x_3207_ = l_Lean_MessageData_ofFormat(v___x_3206_);
    return v___x_3207_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3208_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
    v___x_3209_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__2;
    v___x_3210_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3210_, 0, v___x_3209_);
    crate::leanh::lean_ctor_set(v___x_3210_, 1, v___x_3208_);
    return v___x_3210_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg(
    mut v_ref_3211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3213_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
    v___x_3214_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3214_, 0, v_ref_3211_);
    crate::leanh::lean_ctor_set(v___x_3214_, 1, v___x_3213_);
    v___x_3215_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3215_, 0, v___x_3214_);
    return v___x_3215_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg___boxed(
    mut v_ref_3216_: *mut crate::leanh::LeanObject,
    mut v___y_3217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3218_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_3216_);
    return v_res_3218_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg(
    mut v_x_3219_: *mut crate::leanh::LeanObject,
    mut v___y_3220_: *mut crate::leanh::LeanObject,
    mut v___y_3221_: *mut crate::leanh::LeanObject,
    mut v___y_3222_: *mut crate::leanh::LeanObject,
    mut v___y_3223_: *mut crate::leanh::LeanObject,
    mut v___y_3224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3231_: u8 = 0;
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3235_: u8 = 0;
    let mut v___y_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3240_: u8 = 0;
    let mut v___y_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3251_: u8 = 0;
    let mut v___y_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3269_: u8 = 0;
    let mut v_cancelTk_x3f_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3271_: u8 = 0;
    let mut v_inheritedTraceOptions_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: u8 = 0;
    let mut v___x_3276_: u8 = 0;
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: u8 = 0;
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                v_fileName_3257_ = crate::leanh::lean_ctor_get(v___y_3223_, 0);
                v_fileMap_3258_ = crate::leanh::lean_ctor_get(v___y_3223_, 1);
                v_options_3259_ = crate::leanh::lean_ctor_get(v___y_3223_, 2);
                v_currRecDepth_3260_ = crate::leanh::lean_ctor_get(v___y_3223_, 3);
                v_maxRecDepth_3261_ = crate::leanh::lean_ctor_get(v___y_3223_, 4);
                v_ref_3262_ = crate::leanh::lean_ctor_get(v___y_3223_, 5);
                v_currNamespace_3263_ = crate::leanh::lean_ctor_get(v___y_3223_, 6);
                v_openDecls_3264_ = crate::leanh::lean_ctor_get(v___y_3223_, 7);
                v_initHeartbeats_3265_ = crate::leanh::lean_ctor_get(v___y_3223_, 8);
                v_maxHeartbeats_3266_ = crate::leanh::lean_ctor_get(v___y_3223_, 9);
                v_quotContext_3267_ = crate::leanh::lean_ctor_get(v___y_3223_, 10);
                v_currMacroScope_3268_ = crate::leanh::lean_ctor_get(v___y_3223_, 11);
                v_diag_3269_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3223_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_3270_ = crate::leanh::lean_ctor_get(v___y_3223_, 12);
                v_suppressElabErrors_3271_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3223_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_3272_ = crate::leanh::lean_ctor_get(v___y_3223_, 13);
                if crate::leanh::lean_obj_tag(v_cancelTk_x3f_3270_) == 1 {
                    v_val_3278_ = crate::leanh::lean_ctor_get(v_cancelTk_x3f_3270_, 0);
                    v___x_3279_ = l_IO_CancelToken_isSet(v_val_3278_);
                    if v___x_3279_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_x_3219_);
                        v___x_3280_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg();
                        v_a_3281_ = crate::leanh::lean_ctor_get(v___x_3280_, 0);
                        v_isSharedCheck_3288_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3280_)) as u8;
                        if v_isSharedCheck_3288_ == 0 {
                            v___x_3283_ = v___x_3280_;
                            v_isShared_3284_ = v_isSharedCheck_3288_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3281_);
                            crate::leanh::lean_dec(v___x_3280_);
                            v___x_3283_ = crate::leanh::lean_box(0);
                            v_isShared_3284_ = v_isSharedCheck_3288_;
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
                if crate::leanh::lean_obj_tag(v___y_3227_) == 0 {
                    return v___y_3227_;
                } else {
                    v_a_3228_ = crate::leanh::lean_ctor_get(v___y_3227_, 0);
                    v_isSharedCheck_3235_ = (!crate::leanh::lean_is_exclusive(v___y_3227_)) as u8;
                    if v_isSharedCheck_3235_ == 0 {
                        v___x_3230_ = v___y_3227_;
                        v_isShared_3231_ = v_isSharedCheck_3235_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3228_);
                        crate::leanh::lean_dec(v___y_3227_);
                        v___x_3230_ = crate::leanh::lean_box(0);
                        v_isShared_3231_ = v_isSharedCheck_3235_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3231_ == 0 {
                    v___x_3233_ = v___x_3230_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3234_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_a_3228_);
                    v___x_3233_ = v_reuseFailAlloc_3234_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3233_;
            }
            4 => {
                v___x_3253_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3254_ = lean_nat_add(v___y_3250_, v___x_3253_);
                crate::leanh::lean_inc_ref(v___y_3238_);
                crate::leanh::lean_inc(v___y_3247_);
                crate::leanh::lean_inc(v___y_3246_);
                crate::leanh::lean_inc(v___y_3242_);
                crate::leanh::lean_inc(v___y_3249_);
                crate::leanh::lean_inc(v___y_3237_);
                crate::leanh::lean_inc(v___y_3243_);
                crate::leanh::lean_inc(v___y_3239_);
                crate::leanh::lean_inc(v___y_3245_);
                crate::leanh::lean_inc_ref(v___y_3241_);
                crate::leanh::lean_inc_ref(v___y_3252_);
                crate::leanh::lean_inc_ref(v___y_3248_);
                v___x_3255_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_3255_, 0, v___y_3248_);
                crate::leanh::lean_ctor_set(v___x_3255_, 1, v___y_3252_);
                crate::leanh::lean_ctor_set(v___x_3255_, 2, v___y_3241_);
                crate::leanh::lean_ctor_set(v___x_3255_, 3, v___x_3254_);
                crate::leanh::lean_ctor_set(v___x_3255_, 4, v___y_3245_);
                crate::leanh::lean_ctor_set(v___x_3255_, 5, v___y_3244_);
                crate::leanh::lean_ctor_set(v___x_3255_, 6, v___y_3239_);
                crate::leanh::lean_ctor_set(v___x_3255_, 7, v___y_3243_);
                crate::leanh::lean_ctor_set(v___x_3255_, 8, v___y_3237_);
                crate::leanh::lean_ctor_set(v___x_3255_, 9, v___y_3249_);
                crate::leanh::lean_ctor_set(v___x_3255_, 10, v___y_3242_);
                crate::leanh::lean_ctor_set(v___x_3255_, 11, v___y_3246_);
                crate::leanh::lean_ctor_set(v___x_3255_, 12, v___y_3247_);
                crate::leanh::lean_ctor_set(v___x_3255_, 13, v___y_3238_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3255_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v___y_3251_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3255_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v___y_3240_,
                );
                crate::leanh::lean_inc(v___y_3224_);
                crate::leanh::lean_inc(v___y_3222_);
                crate::leanh::lean_inc_ref(v___y_3221_);
                crate::leanh::lean_inc(v___y_3220_);
                v___x_3256_ = crate::leanh::lean_apply_6(
                    v_x_3219_,
                    v___y_3220_,
                    v___y_3221_,
                    v___y_3222_,
                    v___x_3255_,
                    v___y_3224_,
                    crate::leanh::lean_box(0),
                );
                v___y_3227_ = v___x_3256_;
                state = 1;
                continue;
            }
            5 => {
                v___x_3274_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3275_ = lean_nat_dec_eq(v_maxRecDepth_3261_, v___x_3274_);
                if v___x_3275_ == 0 {
                    v___x_3276_ = lean_nat_dec_eq(v_currRecDepth_3260_, v_maxRecDepth_3261_);
                    if v___x_3276_ == 0 {
                        crate::leanh::lean_inc(v_ref_3262_);
                        v___y_3237_ = v_initHeartbeats_3265_;
                        v___y_3238_ = v_inheritedTraceOptions_3272_;
                        v___y_3239_ = v_currNamespace_3263_;
                        v___y_3240_ = v_suppressElabErrors_3271_;
                        v___y_3241_ = v_options_3259_;
                        v___y_3242_ = v_quotContext_3267_;
                        v___y_3243_ = v_openDecls_3264_;
                        v___y_3244_ = v_ref_3262_;
                        v___y_3245_ = v_maxRecDepth_3261_;
                        v___y_3246_ = v_currMacroScope_3268_;
                        v___y_3247_ = v_cancelTk_x3f_3270_;
                        v___y_3248_ = v_fileName_3257_;
                        v___y_3249_ = v_maxHeartbeats_3266_;
                        v___y_3250_ = v_currRecDepth_3260_;
                        v___y_3251_ = v_diag_3269_;
                        v___y_3252_ = v_fileMap_3258_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_x_3219_);
                        crate::leanh::lean_inc(v_ref_3262_);
                        v___x_3277_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_3262_);
                        v___y_3227_ = v___x_3277_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_ref_3262_);
                    v___y_3237_ = v_initHeartbeats_3265_;
                    v___y_3238_ = v_inheritedTraceOptions_3272_;
                    v___y_3239_ = v_currNamespace_3263_;
                    v___y_3240_ = v_suppressElabErrors_3271_;
                    v___y_3241_ = v_options_3259_;
                    v___y_3242_ = v_quotContext_3267_;
                    v___y_3243_ = v_openDecls_3264_;
                    v___y_3244_ = v_ref_3262_;
                    v___y_3245_ = v_maxRecDepth_3261_;
                    v___y_3246_ = v_currMacroScope_3268_;
                    v___y_3247_ = v_cancelTk_x3f_3270_;
                    v___y_3248_ = v_fileName_3257_;
                    v___y_3249_ = v_maxHeartbeats_3266_;
                    v___y_3250_ = v_currRecDepth_3260_;
                    v___y_3251_ = v_diag_3269_;
                    v___y_3252_ = v_fileMap_3258_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                if v_isShared_3284_ == 0 {
                    v___x_3286_ = v___x_3283_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3287_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
                    v___x_3286_ = v_reuseFailAlloc_3287_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3286_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg___boxed(
    mut v_x_3289_: *mut crate::leanh::LeanObject,
    mut v___y_3290_: *mut crate::leanh::LeanObject,
    mut v___y_3291_: *mut crate::leanh::LeanObject,
    mut v___y_3292_: *mut crate::leanh::LeanObject,
    mut v___y_3293_: *mut crate::leanh::LeanObject,
    mut v___y_3294_: *mut crate::leanh::LeanObject,
    mut v___y_3295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3296_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg(v_x_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
    crate::leanh::lean_dec(v___y_3294_);
    crate::leanh::lean_dec_ref(v___y_3293_);
    crate::leanh::lean_dec(v___y_3292_);
    crate::leanh::lean_dec_ref(v___y_3291_);
    crate::leanh::lean_dec(v___y_3290_);
    return v_res_3296_;
}
pub unsafe fn _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3298_ = crate::leanh::lean_box(0);
    v_dummy_3299_ = l_Lean_Expr_sort___override(v___x_3298_);
    return v_dummy_3299_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1(
    mut v_pre_3300_: *mut crate::leanh::LeanObject,
    mut v_post_3301_: *mut crate::leanh::LeanObject,
    mut v_sz_3302_: usize,
    mut v_i_3303_: usize,
    mut v_bs_3304_: *mut crate::leanh::LeanObject,
    mut v___y_3305_: *mut crate::leanh::LeanObject,
    mut v___y_3306_: *mut crate::leanh::LeanObject,
    mut v___y_3307_: *mut crate::leanh::LeanObject,
    mut v___y_3308_: *mut crate::leanh::LeanObject,
    mut v___y_3309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3311_: u8 = 0;
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: usize = 0;
    let mut v___x_3319_: usize = 0;
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3325_: u8 = 0;
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3329_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3311_ = lean_usize_dec_lt(v_i_3303_, v_sz_3302_);
                if v___x_3311_ == 0 {
                    crate::leanh::lean_dec_ref(v_post_3301_);
                    crate::leanh::lean_dec_ref(v_pre_3300_);
                    v___x_3312_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3312_, 0, v_bs_3304_);
                    return v___x_3312_;
                } else {
                    v_v_3313_ = lean_array_uget_borrowed(v_bs_3304_, v_i_3303_);
                    crate::leanh::lean_inc(v_v_3313_);
                    crate::leanh::lean_inc_ref(v_post_3301_);
                    crate::leanh::lean_inc_ref(v_pre_3300_);
                    v___x_3314_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_3300_, v_post_3301_, v_v_3313_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
                    if crate::leanh::lean_obj_tag(v___x_3314_) == 0 {
                        v_a_3315_ = crate::leanh::lean_ctor_get(v___x_3314_, 0);
                        crate::leanh::lean_inc(v_a_3315_);
                        crate::leanh::lean_dec_ref_known(v___x_3314_, 1);
                        v___x_3316_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_3317_ = lean_array_uset(v_bs_3304_, v_i_3303_, v___x_3316_);
                        v___x_3318_ = 1usize;
                        v___x_3319_ = lean_usize_add(v_i_3303_, v___x_3318_);
                        v___x_3320_ = lean_array_uset(v_bs_x27_3317_, v_i_3303_, v_a_3315_);
                        v_i_3303_ = v___x_3319_;
                        v_bs_3304_ = v___x_3320_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_3304_);
                        crate::leanh::lean_dec_ref(v_post_3301_);
                        crate::leanh::lean_dec_ref(v_pre_3300_);
                        v_a_3322_ = crate::leanh::lean_ctor_get(v___x_3314_, 0);
                        v_isSharedCheck_3329_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3314_)) as u8;
                        if v_isSharedCheck_3329_ == 0 {
                            v___x_3324_ = v___x_3314_;
                            v_isShared_3325_ = v_isSharedCheck_3329_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3322_);
                            crate::leanh::lean_dec(v___x_3314_);
                            v___x_3324_ = crate::leanh::lean_box(0);
                            v_isShared_3325_ = v_isSharedCheck_3329_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3325_ == 0 {
                    v___x_3327_ = v___x_3324_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3328_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3322_);
                    v___x_3327_ = v_reuseFailAlloc_3328_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3327_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4(
    mut v_pre_3330_: *mut crate::leanh::LeanObject,
    mut v_post_3331_: *mut crate::leanh::LeanObject,
    mut v_x_3332_: *mut crate::leanh::LeanObject,
    mut v_x_3333_: *mut crate::leanh::LeanObject,
    mut v_x_3334_: *mut crate::leanh::LeanObject,
    mut v___y_3335_: *mut crate::leanh::LeanObject,
    mut v___y_3336_: *mut crate::leanh::LeanObject,
    mut v___y_3337_: *mut crate::leanh::LeanObject,
    mut v___y_3338_: *mut crate::leanh::LeanObject,
    mut v___y_3339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3349_: usize = 0;
    let mut v___x_3350_: usize = 0;
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3358_: u8 = 0;
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3362_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3332_) == 5 {
                    v_fn_3341_ = crate::leanh::lean_ctor_get(v_x_3332_, 0);
                    crate::leanh::lean_inc_ref(v_fn_3341_);
                    v_arg_3342_ = crate::leanh::lean_ctor_get(v_x_3332_, 1);
                    crate::leanh::lean_inc_ref(v_arg_3342_);
                    crate::leanh::lean_dec_ref_known(v_x_3332_, 2);
                    v___x_3343_ = lean_array_set(v_x_3333_, v_x_3334_, v_arg_3342_);
                    v___x_3344_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3345_ = lean_nat_sub(v_x_3334_, v___x_3344_);
                    crate::leanh::lean_dec(v_x_3334_);
                    v_x_3332_ = v_fn_3341_;
                    v_x_3333_ = v___x_3343_;
                    v_x_3334_ = v___x_3345_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_3334_);
                    crate::leanh::lean_inc_ref(v_post_3331_);
                    crate::leanh::lean_inc_ref(v_pre_3330_);
                    v___x_3347_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_3330_, v_post_3331_, v_x_3332_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
                    if crate::leanh::lean_obj_tag(v___x_3347_) == 0 {
                        v_a_3348_ = crate::leanh::lean_ctor_get(v___x_3347_, 0);
                        crate::leanh::lean_inc(v_a_3348_);
                        crate::leanh::lean_dec_ref_known(v___x_3347_, 1);
                        v_sz_3349_ = lean_array_size(v_x_3333_);
                        v___x_3350_ = 0usize;
                        crate::leanh::lean_inc_ref(v_post_3331_);
                        crate::leanh::lean_inc_ref(v_pre_3330_);
                        v___x_3351_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1(v_pre_3330_, v_post_3331_, v_sz_3349_, v___x_3350_, v_x_3333_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
                        if crate::leanh::lean_obj_tag(v___x_3351_) == 0 {
                            v_a_3352_ = crate::leanh::lean_ctor_get(v___x_3351_, 0);
                            crate::leanh::lean_inc(v_a_3352_);
                            crate::leanh::lean_dec_ref_known(v___x_3351_, 1);
                            v___x_3353_ = l_Lean_mkAppN(v_a_3348_, v_a_3352_);
                            crate::leanh::lean_dec(v_a_3352_);
                            v___x_3354_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_3330_, v_post_3331_, v___x_3353_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
                            return v___x_3354_;
                        } else {
                            crate::leanh::lean_dec(v_a_3348_);
                            crate::leanh::lean_dec_ref(v_post_3331_);
                            crate::leanh::lean_dec_ref(v_pre_3330_);
                            v_a_3355_ = crate::leanh::lean_ctor_get(v___x_3351_, 0);
                            v_isSharedCheck_3362_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3351_)) as u8;
                            if v_isSharedCheck_3362_ == 0 {
                                v___x_3357_ = v___x_3351_;
                                v_isShared_3358_ = v_isSharedCheck_3362_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3355_);
                                crate::leanh::lean_dec(v___x_3351_);
                                v___x_3357_ = crate::leanh::lean_box(0);
                                v_isShared_3358_ = v_isSharedCheck_3362_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_3333_);
                        crate::leanh::lean_dec_ref(v_post_3331_);
                        crate::leanh::lean_dec_ref(v_pre_3330_);
                        return v___x_3347_;
                    }
                }
            }
            1 => {
                if v_isShared_3358_ == 0 {
                    v___x_3360_ = v___x_3357_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3361_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_a_3355_);
                    v___x_3360_ = v_reuseFailAlloc_3361_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3360_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1(
    mut v___x_3363_: *mut crate::leanh::LeanObject,
    mut v_pre_3364_: *mut crate::leanh::LeanObject,
    mut v_e_3365_: *mut crate::leanh::LeanObject,
    mut v_post_3366_: *mut crate::leanh::LeanObject,
    mut v___y_3367_: *mut crate::leanh::LeanObject,
    mut v___y_3368_: *mut crate::leanh::LeanObject,
    mut v___y_3369_: *mut crate::leanh::LeanObject,
    mut v___y_3370_: *mut crate::leanh::LeanObject,
    mut v___y_3371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3379_: u8 = 0;
    let mut v___y_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3381_: u8 = 0;
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: usize = 0;
    let mut v___x_3385_: usize = 0;
    let mut v___x_3386_: u8 = 0;
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3391_: u8 = 0;
    let mut v___y_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3396_: u8 = 0;
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: u8 = 0;
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3407_: u8 = 0;
    let mut v___y_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3409_: u8 = 0;
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: u8 = 0;
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3421_: u8 = 0;
    let mut v___y_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3427_: u8 = 0;
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: usize = 0;
    let mut v___x_3433_: usize = 0;
    let mut v___x_3434_: u8 = 0;
    let mut v___x_3435_: usize = 0;
    let mut v___x_3436_: usize = 0;
    let mut v___x_3437_: u8 = 0;
    let mut v_binderName_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3441_: u8 = 0;
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: usize = 0;
    let mut v___x_3447_: usize = 0;
    let mut v___x_3448_: u8 = 0;
    let mut v___x_3449_: usize = 0;
    let mut v___x_3450_: usize = 0;
    let mut v___x_3451_: u8 = 0;
    let mut v_declName_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_3456_: u8 = 0;
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: usize = 0;
    let mut v___x_3464_: usize = 0;
    let mut v___x_3465_: u8 = 0;
    let mut v___x_3466_: usize = 0;
    let mut v___x_3467_: usize = 0;
    let mut v___x_3468_: u8 = 0;
    let mut v_dummy_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: usize = 0;
    let mut v___x_3480_: usize = 0;
    let mut v___x_3481_: u8 = 0;
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: usize = 0;
    let mut v___x_3491_: usize = 0;
    let mut v___x_3492_: u8 = 0;
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3507_: u8 = 0;
    let mut v_a_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3511_: u8 = 0;
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3515_: u8 = 0;
    let mut v_a_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3519_: u8 = 0;
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3523_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3416_ = l_Lean_Core_checkSystem(v___x_3363_, v___y_3370_, v___y_3371_);
                if crate::leanh::lean_obj_tag(v___x_3416_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3416_, 1);
                    crate::leanh::lean_inc_ref(v_pre_3364_);
                    crate::leanh::lean_inc(v___y_3371_);
                    crate::leanh::lean_inc_ref(v___y_3370_);
                    crate::leanh::lean_inc(v___y_3369_);
                    crate::leanh::lean_inc_ref(v___y_3368_);
                    crate::leanh::lean_inc_ref(v_e_3365_);
                    v___x_3417_ = crate::leanh::lean_apply_6(
                        v_pre_3364_,
                        v_e_3365_,
                        v___y_3368_,
                        v___y_3369_,
                        v___y_3370_,
                        v___y_3371_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3417_) == 0 {
                        v_a_3418_ = crate::leanh::lean_ctor_get(v___x_3417_, 0);
                        v_isSharedCheck_3507_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3417_)) as u8;
                        if v_isSharedCheck_3507_ == 0 {
                            v___x_3420_ = v___x_3417_;
                            v_isShared_3421_ = v_isSharedCheck_3507_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3418_);
                            crate::leanh::lean_dec(v___x_3417_);
                            v___x_3420_ = crate::leanh::lean_box(0);
                            v_isShared_3421_ = v_isSharedCheck_3507_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_post_3366_);
                        crate::leanh::lean_dec_ref(v_e_3365_);
                        crate::leanh::lean_dec_ref(v_pre_3364_);
                        v_a_3508_ = crate::leanh::lean_ctor_get(v___x_3417_, 0);
                        v_isSharedCheck_3515_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3417_)) as u8;
                        if v_isSharedCheck_3515_ == 0 {
                            v___x_3510_ = v___x_3417_;
                            v_isShared_3511_ = v_isSharedCheck_3515_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3508_);
                            crate::leanh::lean_dec(v___x_3417_);
                            v___x_3510_ = crate::leanh::lean_box(0);
                            v_isShared_3511_ = v_isSharedCheck_3515_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_post_3366_);
                    crate::leanh::lean_dec_ref(v_e_3365_);
                    crate::leanh::lean_dec_ref(v_pre_3364_);
                    v_a_3516_ = crate::leanh::lean_ctor_get(v___x_3416_, 0);
                    v_isSharedCheck_3523_ = (!crate::leanh::lean_is_exclusive(v___x_3416_)) as u8;
                    if v_isSharedCheck_3523_ == 0 {
                        v___x_3518_ = v___x_3416_;
                        v_isShared_3519_ = v_isSharedCheck_3523_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3516_);
                        crate::leanh::lean_dec(v___x_3416_);
                        v___x_3518_ = crate::leanh::lean_box(0);
                        v_isShared_3519_ = v_isSharedCheck_3523_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_3381_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_3380_);
                    crate::leanh::lean_dec_ref(v___y_3376_);
                    v___x_3382_ = l_Lean_Expr_letE___override(
                        v___y_3375_,
                        v___y_3377_,
                        v___y_3378_,
                        v___y_3374_,
                        v___y_3379_,
                    );
                    v___x_3383_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_3364_, v_post_3366_, v___x_3382_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
                    return v___x_3383_;
                } else {
                    v___x_3384_ = lean_ptr_addr(v___y_3380_);
                    crate::leanh::lean_dec_ref(v___y_3380_);
                    v___x_3385_ = lean_ptr_addr(v___y_3374_);
                    v___x_3386_ = lean_usize_dec_eq(v___x_3384_, v___x_3385_);
                    if v___x_3386_ == 0 {
                        crate::leanh::lean_dec_ref(v___y_3376_);
                        v___x_3387_ = l_Lean_Expr_letE___override(
                            v___y_3375_,
                            v___y_3377_,
                            v___y_3378_,
                            v___y_3374_,
                            v___y_3379_,
                        );
                        v___x_3388_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_3364_, v_post_3366_, v___x_3387_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
                        return v___x_3388_;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_3378_);
                        crate::leanh::lean_dec_ref(v___y_3377_);
                        crate::leanh::lean_dec(v___y_3375_);
                        crate::leanh::lean_dec_ref(v___y_3374_);
                        v___x_3389_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_3364_, v_post_3366_, v___y_3376_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
                        return v___x_3389_;
                    }
                }
            }
            2 => {
                if v___y_3396_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_3393_);
                    v___x_3397_ = l_Lean_Expr_lam___override(
                        v___y_3395_,
                        v___y_3394_,
                        v___y_3392_,
                        v___y_3391_,
                    );
                    v___x_3398_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_3364_, v_post_3366_, v___x_3397_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
                    return v___x_3398_;
                } else {
                    v___x_3399_ = l_Lean_instBEqBinderInfo_beq(v___y_3391_, v___y_3391_);
                    if v___x_3399_ == 0 {
                        crate::leanh::lean_dec_ref(v___y_3393_);
                        v___x_3400_ = l_Lean_Expr_lam___override(
                            v___y_3395_,
                            v___y_3394_,
                            v___y_3392_,
                            v___y_3391_,
                        );
                        v___x_3401_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_3364_, v_post_3366_, v___x_3400_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
                        return v___x_3401_;
                    } else {
                        crate::leanh::lean_dec(v___y_3395_);
                        crate::leanh::lean_dec_ref(v___y_3394_);
                        crate::leanh::lean_dec_ref(v___y_3392_);
                        v___x_3402_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_3364_, v_post_3366_, v___y_3393_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
                        return v___x_3402_;
                    }
                }
            }
            3 => {
                if v___y_3409_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_3405_);
                    v___x_3410_ = l_Lean_Expr_forallE___override(
                        v___y_3404_,
                        v___y_3408_,
                        v___y_3406_,
                        v___y_3407_,
                    );
                    v___x_3411_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_3364_, v_post_3366_, v___x_3410_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
                    return v___x_3411_;
                } else {
                    v___x_3412_ = l_Lean_instBEqBinderInfo_beq(v___y_3407_, v___y_3407_);
                    if v___x_3412_ == 0 {
                        crate::leanh::lean_dec_ref(v___y_3405_);
                        v___x_3413_ = l_Lean_Expr_forallE___override(
                            v___y_3404_,
                            v___y_3408_,
                            v___y_3406_,
                            v___y_3407_,
                        );
                        v___x_3414_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_3364_, v_post_3366_, v___x_3413_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
                        return v___x_3414_;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_3408_);
                        crate::leanh::lean_dec_ref(v___y_3406_);
                        crate::leanh::lean_dec(v___y_3404_);
                        v___x_3415_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_3364_, v_post_3366_, v___y_3405_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
                        return v___x_3415_;
                    }
                }
            }
            4 => match crate::leanh::lean_obj_tag(v_a_3418_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_post_3366_);
                    crate::leanh::lean_dec_ref(v_e_3365_);
                    crate::leanh::lean_dec_ref(v_pre_3364_);
                    v_e_3497_ = crate::leanh::lean_ctor_get(v_a_3418_, 0);
                    crate::leanh::lean_inc_ref(v_e_3497_);
                    crate::leanh::lean_dec_ref_known(v_a_3418_, 1);
                    if v_isShared_3421_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3420_, 0, v_e_3497_);
                        v___x_3499_ = v___x_3420_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3500_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_e_3497_);
                        v___x_3499_ = v_reuseFailAlloc_3500_;
                        state = 6;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_3420_);
                    crate::leanh::lean_dec_ref(v_e_3365_);
                    v_e_3501_ = crate::leanh::lean_ctor_get(v_a_3418_, 0);
                    crate::leanh::lean_inc_ref(v_e_3501_);
                    crate::leanh::lean_dec_ref_known(v_a_3418_, 1);
                    crate::leanh::lean_inc_ref(v_post_3366_);
                    crate::leanh::lean_inc_ref(v_pre_3364_);
                    v___x_3502_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_3364_, v_post_3366_, v_e_3501_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
                    if crate::leanh::lean_obj_tag(v___x_3502_) == 0 {
                        v_a_3503_ = crate::leanh::lean_ctor_get(v___x_3502_, 0);
                        crate::leanh::lean_inc(v_a_3503_);
                        crate::leanh::lean_dec_ref_known(v___x_3502_, 1);
                        v___x_3504_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_3364_, v_post_3366_, v_a_3503_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
                        return v___x_3504_;
                    } else {
                        crate::leanh::lean_dec_ref(v_post_3366_);
                        crate::leanh::lean_dec_ref(v_pre_3364_);
                        return v___x_3502_;
                    }
                }
                _ => {
                    crate::leanh::lean_del_object(v___x_3420_);
                    v_e_x3f_3505_ = crate::leanh::lean_ctor_get(v_a_3418_, 0);
                    crate::leanh::lean_inc(v_e_x3f_3505_);
                    crate::leanh::lean_dec_ref_known(v_a_3418_, 1);
                    if crate::leanh::lean_obj_tag(v_e_x3f_3505_) == 0 {
                        v___y_3423_ = v_e_3365_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_e_3365_);
                        v_val_3506_ = crate::leanh::lean_ctor_get(v_e_x3f_3505_, 0);
                        crate::leanh::lean_inc(v_val_3506_);
                        crate::leanh::lean_dec_ref_known(v_e_x3f_3505_, 1);
                        v___y_3423_ = v_val_3506_;
                        state = 5;
                        continue;
                    }
                }
            },
            5 => match crate::leanh::lean_obj_tag(v___y_3423_) {
                7 => {
                    v_binderName_3424_ = crate::leanh::lean_ctor_get(v___y_3423_, 0);
                    crate::leanh::lean_inc(v_binderName_3424_);
                    v_binderType_3425_ = crate::leanh::lean_ctor_get(v___y_3423_, 1);
                    v_body_3426_ = crate::leanh::lean_ctor_get(v___y_3423_, 2);
                    v_binderInfo_3427_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_3423_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc_ref(v_binderType_3425_);
                    crate::leanh::lean_inc_ref(v_post_3366_);
                    crate::leanh::lean_inc_ref(v_pre_3364_);
                    v___x_3428_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_3364_, v_post_3366_, v_binderType_3425_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
                    if crate::leanh::lean_obj_tag(v___x_3428_) == 0 {
                        v_a_3429_ = crate::leanh::lean_ctor_get(v___x_3428_, 0);
                        crate::leanh::lean_inc(v_a_3429_);
                        crate::leanh::lean_dec_ref_known(v___x_3428_, 1);
                        crate::leanh::lean_inc_ref(v_body_3426_);
                        crate::leanh::lean_inc_ref(v_post_3366_);
                        crate::leanh::lean_inc_ref(v_pre_3364_);
                        v___x_3430_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_3364_, v_post_3366_, v_body_3426_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
                        if crate::leanh::lean_obj_tag(v___x_3430_) == 0 {
                            v_a_3431_ = crate::leanh::lean_ctor_get(v___x_3430_, 0);
                            crate::leanh::lean_inc(v_a_3431_);
                            crate::leanh::lean_dec_ref_known(v___x_3430_, 1);
                            v___x_3432_ = lean_ptr_addr(v_binderType_3425_);
                            v___x_3433_ = lean_ptr_addr(v_a_3429_);
                            v___x_3434_ = lean_usize_dec_eq(v___x_3432_, v___x_3433_);
                            if v___x_3434_ == 0 {
                                v___y_3404_ = v_binderName_3424_;
                                v___y_3405_ = v___y_3423_;
                                v___y_3406_ = v_a_3431_;
                                v___y_3407_ = v_binderInfo_3427_;
                                v___y_3408_ = v_a_3429_;
                                v___y_3409_ = v___x_3434_;
                                state = 3;
                                continue;
                            } else {
                                v___x_3435_ = lean_ptr_addr(v_body_3426_);
                                v___x_3436_ = lean_ptr_addr(v_a_3431_);
                                v___x_3437_ = lean_usize_dec_eq(v___x_3435_, v___x_3436_);
                                v___y_3404_ = v_binderName_3424_;
                                v___y_3405_ = v___y_3423_;
                                v___y_3406_ = v_a_3431_;
                                v___y_3407_ = v_binderInfo_3427_;
                                v___y_3408_ = v_a_3429_;
                                v___y_3409_ = v___x_3437_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3429_);
                            crate::leanh::lean_dec_ref_known(v___y_3423_, 3);
                            crate::leanh::lean_dec(v_binderName_3424_);
                            crate::leanh::lean_dec_ref(v_post_3366_);
                            crate::leanh::lean_dec_ref(v_pre_3364_);
                            return v___x_3430_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_3423_, 3);
                        crate::leanh::lean_dec(v_binderName_3424_);
                        crate::leanh::lean_dec_ref(v_post_3366_);
                        crate::leanh::lean_dec_ref(v_pre_3364_);
                        return v___x_3428_;
                    }
                }
                6 => {
                    v_binderName_3438_ = crate::leanh::lean_ctor_get(v___y_3423_, 0);
                    crate::leanh::lean_inc(v_binderName_3438_);
                    v_binderType_3439_ = crate::leanh::lean_ctor_get(v___y_3423_, 1);
                    v_body_3440_ = crate::leanh::lean_ctor_get(v___y_3423_, 2);
                    v_binderInfo_3441_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_3423_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc_ref(v_binderType_3439_);
                    crate::leanh::lean_inc_ref(v_post_3366_);
                    crate::leanh::lean_inc_ref(v_pre_3364_);
                    v___x_3442_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_3364_, v_post_3366_, v_binderType_3439_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
                    if crate::leanh::lean_obj_tag(v___x_3442_) == 0 {
                        v_a_3443_ = crate::leanh::lean_ctor_get(v___x_3442_, 0);
                        crate::leanh::lean_inc(v_a_3443_);
                        crate::leanh::lean_dec_ref_known(v___x_3442_, 1);
                        crate::leanh::lean_inc_ref(v_body_3440_);
                        crate::leanh::lean_inc_ref(v_post_3366_);
                        crate::leanh::lean_inc_ref(v_pre_3364_);
                        v___x_3444_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_3364_, v_post_3366_, v_body_3440_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
                        if crate::leanh::lean_obj_tag(v___x_3444_) == 0 {
                            v_a_3445_ = crate::leanh::lean_ctor_get(v___x_3444_, 0);
                            crate::leanh::lean_inc(v_a_3445_);
                            crate::leanh::lean_dec_ref_known(v___x_3444_, 1);
                            v___x_3446_ = lean_ptr_addr(v_binderType_3439_);
                            v___x_3447_ = lean_ptr_addr(v_a_3443_);
                            v___x_3448_ = lean_usize_dec_eq(v___x_3446_, v___x_3447_);
                            if v___x_3448_ == 0 {
                                v___y_3391_ = v_binderInfo_3441_;
                                v___y_3392_ = v_a_3445_;
                                v___y_3393_ = v___y_3423_;
                                v___y_3394_ = v_a_3443_;
                                v___y_3395_ = v_binderName_3438_;
                                v___y_3396_ = v___x_3448_;
                                state = 2;
                                continue;
                            } else {
                                v___x_3449_ = lean_ptr_addr(v_body_3440_);
                                v___x_3450_ = lean_ptr_addr(v_a_3445_);
                                v___x_3451_ = lean_usize_dec_eq(v___x_3449_, v___x_3450_);
                                v___y_3391_ = v_binderInfo_3441_;
                                v___y_3392_ = v_a_3445_;
                                v___y_3393_ = v___y_3423_;
                                v___y_3394_ = v_a_3443_;
                                v___y_3395_ = v_binderName_3438_;
                                v___y_3396_ = v___x_3451_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3443_);
                            crate::leanh::lean_dec_ref_known(v___y_3423_, 3);
                            crate::leanh::lean_dec(v_binderName_3438_);
                            crate::leanh::lean_dec_ref(v_post_3366_);
                            crate::leanh::lean_dec_ref(v_pre_3364_);
                            return v___x_3444_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_3423_, 3);
                        crate::leanh::lean_dec(v_binderName_3438_);
                        crate::leanh::lean_dec_ref(v_post_3366_);
                        crate::leanh::lean_dec_ref(v_pre_3364_);
                        return v___x_3442_;
                    }
                }
                8 => {
                    v_declName_3452_ = crate::leanh::lean_ctor_get(v___y_3423_, 0);
                    crate::leanh::lean_inc(v_declName_3452_);
                    v_type_3453_ = crate::leanh::lean_ctor_get(v___y_3423_, 1);
                    v_value_3454_ = crate::leanh::lean_ctor_get(v___y_3423_, 2);
                    v_body_3455_ = crate::leanh::lean_ctor_get(v___y_3423_, 3);
                    crate::leanh::lean_inc_ref(v_body_3455_);
                    v_nondep_3456_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_3423_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    crate::leanh::lean_inc_ref(v_type_3453_);
                    crate::leanh::lean_inc_ref(v_post_3366_);
                    crate::leanh::lean_inc_ref(v_pre_3364_);
                    v___x_3457_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_3364_, v_post_3366_, v_type_3453_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
                    if crate::leanh::lean_obj_tag(v___x_3457_) == 0 {
                        v_a_3458_ = crate::leanh::lean_ctor_get(v___x_3457_, 0);
                        crate::leanh::lean_inc(v_a_3458_);
                        crate::leanh::lean_dec_ref_known(v___x_3457_, 1);
                        crate::leanh::lean_inc_ref(v_value_3454_);
                        crate::leanh::lean_inc_ref(v_post_3366_);
                        crate::leanh::lean_inc_ref(v_pre_3364_);
                        v___x_3459_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_3364_, v_post_3366_, v_value_3454_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
                        if crate::leanh::lean_obj_tag(v___x_3459_) == 0 {
                            v_a_3460_ = crate::leanh::lean_ctor_get(v___x_3459_, 0);
                            crate::leanh::lean_inc(v_a_3460_);
                            crate::leanh::lean_dec_ref_known(v___x_3459_, 1);
                            crate::leanh::lean_inc_ref(v_body_3455_);
                            crate::leanh::lean_inc_ref(v_post_3366_);
                            crate::leanh::lean_inc_ref(v_pre_3364_);
                            v___x_3461_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_3364_, v_post_3366_, v_body_3455_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
                            if crate::leanh::lean_obj_tag(v___x_3461_) == 0 {
                                v_a_3462_ = crate::leanh::lean_ctor_get(v___x_3461_, 0);
                                crate::leanh::lean_inc(v_a_3462_);
                                crate::leanh::lean_dec_ref_known(v___x_3461_, 1);
                                v___x_3463_ = lean_ptr_addr(v_type_3453_);
                                v___x_3464_ = lean_ptr_addr(v_a_3458_);
                                v___x_3465_ = lean_usize_dec_eq(v___x_3463_, v___x_3464_);
                                if v___x_3465_ == 0 {
                                    v___y_3374_ = v_a_3462_;
                                    v___y_3375_ = v_declName_3452_;
                                    v___y_3376_ = v___y_3423_;
                                    v___y_3377_ = v_a_3458_;
                                    v___y_3378_ = v_a_3460_;
                                    v___y_3379_ = v_nondep_3456_;
                                    v___y_3380_ = v_body_3455_;
                                    v___y_3381_ = v___x_3465_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_3466_ = lean_ptr_addr(v_value_3454_);
                                    v___x_3467_ = lean_ptr_addr(v_a_3460_);
                                    v___x_3468_ = lean_usize_dec_eq(v___x_3466_, v___x_3467_);
                                    v___y_3374_ = v_a_3462_;
                                    v___y_3375_ = v_declName_3452_;
                                    v___y_3376_ = v___y_3423_;
                                    v___y_3377_ = v_a_3458_;
                                    v___y_3378_ = v_a_3460_;
                                    v___y_3379_ = v_nondep_3456_;
                                    v___y_3380_ = v_body_3455_;
                                    v___y_3381_ = v___x_3468_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3460_);
                                crate::leanh::lean_dec(v_a_3458_);
                                crate::leanh::lean_dec_ref(v_body_3455_);
                                crate::leanh::lean_dec_ref_known(v___y_3423_, 4);
                                crate::leanh::lean_dec(v_declName_3452_);
                                crate::leanh::lean_dec_ref(v_post_3366_);
                                crate::leanh::lean_dec_ref(v_pre_3364_);
                                return v___x_3461_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3458_);
                            crate::leanh::lean_dec_ref(v_body_3455_);
                            crate::leanh::lean_dec(v_declName_3452_);
                            crate::leanh::lean_dec_ref_known(v___y_3423_, 4);
                            crate::leanh::lean_dec_ref(v_post_3366_);
                            crate::leanh::lean_dec_ref(v_pre_3364_);
                            return v___x_3459_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_body_3455_);
                        crate::leanh::lean_dec(v_declName_3452_);
                        crate::leanh::lean_dec_ref_known(v___y_3423_, 4);
                        crate::leanh::lean_dec_ref(v_post_3366_);
                        crate::leanh::lean_dec_ref(v_pre_3364_);
                        return v___x_3457_;
                    }
                }
                5 => {
                    v_dummy_3469_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0_once), _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___closed__0);
                    v_nargs_3470_ = l_Lean_Expr_getAppNumArgs(v___y_3423_);
                    crate::leanh::lean_inc(v_nargs_3470_);
                    v___x_3471_ = lean_mk_array(v_nargs_3470_, v_dummy_3469_);
                    v___x_3472_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3473_ = lean_nat_sub(v_nargs_3470_, v___x_3472_);
                    crate::leanh::lean_dec(v_nargs_3470_);
                    v___x_3474_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4(v_pre_3364_, v_post_3366_, v___y_3423_, v___x_3471_, v___x_3473_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
                    return v___x_3474_;
                }
                10 => {
                    v_data_3475_ = crate::leanh::lean_ctor_get(v___y_3423_, 0);
                    v_expr_3476_ = crate::leanh::lean_ctor_get(v___y_3423_, 1);
                    crate::leanh::lean_inc_ref(v_expr_3476_);
                    crate::leanh::lean_inc_ref(v_post_3366_);
                    crate::leanh::lean_inc_ref(v_pre_3364_);
                    v___x_3477_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_3364_, v_post_3366_, v_expr_3476_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
                    if crate::leanh::lean_obj_tag(v___x_3477_) == 0 {
                        v_a_3478_ = crate::leanh::lean_ctor_get(v___x_3477_, 0);
                        crate::leanh::lean_inc(v_a_3478_);
                        crate::leanh::lean_dec_ref_known(v___x_3477_, 1);
                        v___x_3479_ = lean_ptr_addr(v_expr_3476_);
                        v___x_3480_ = lean_ptr_addr(v_a_3478_);
                        v___x_3481_ = lean_usize_dec_eq(v___x_3479_, v___x_3480_);
                        if v___x_3481_ == 0 {
                            crate::leanh::lean_inc(v_data_3475_);
                            crate::leanh::lean_dec_ref_known(v___y_3423_, 2);
                            v___x_3482_ = l_Lean_Expr_mdata___override(v_data_3475_, v_a_3478_);
                            v___x_3483_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_3364_, v_post_3366_, v___x_3482_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
                            return v___x_3483_;
                        } else {
                            crate::leanh::lean_dec(v_a_3478_);
                            v___x_3484_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_3364_, v_post_3366_, v___y_3423_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
                            return v___x_3484_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_3423_, 2);
                        crate::leanh::lean_dec_ref(v_post_3366_);
                        crate::leanh::lean_dec_ref(v_pre_3364_);
                        return v___x_3477_;
                    }
                }
                11 => {
                    v_typeName_3485_ = crate::leanh::lean_ctor_get(v___y_3423_, 0);
                    v_idx_3486_ = crate::leanh::lean_ctor_get(v___y_3423_, 1);
                    v_struct_3487_ = crate::leanh::lean_ctor_get(v___y_3423_, 2);
                    crate::leanh::lean_inc_ref(v_struct_3487_);
                    crate::leanh::lean_inc_ref(v_post_3366_);
                    crate::leanh::lean_inc_ref(v_pre_3364_);
                    v___x_3488_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_3364_, v_post_3366_, v_struct_3487_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
                    if crate::leanh::lean_obj_tag(v___x_3488_) == 0 {
                        v_a_3489_ = crate::leanh::lean_ctor_get(v___x_3488_, 0);
                        crate::leanh::lean_inc(v_a_3489_);
                        crate::leanh::lean_dec_ref_known(v___x_3488_, 1);
                        v___x_3490_ = lean_ptr_addr(v_struct_3487_);
                        v___x_3491_ = lean_ptr_addr(v_a_3489_);
                        v___x_3492_ = lean_usize_dec_eq(v___x_3490_, v___x_3491_);
                        if v___x_3492_ == 0 {
                            crate::leanh::lean_inc(v_idx_3486_);
                            crate::leanh::lean_inc(v_typeName_3485_);
                            crate::leanh::lean_dec_ref_known(v___y_3423_, 3);
                            v___x_3493_ = l_Lean_Expr_proj___override(
                                v_typeName_3485_,
                                v_idx_3486_,
                                v_a_3489_,
                            );
                            v___x_3494_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_3364_, v_post_3366_, v___x_3493_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
                            return v___x_3494_;
                        } else {
                            crate::leanh::lean_dec(v_a_3489_);
                            v___x_3495_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_3364_, v_post_3366_, v___y_3423_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
                            return v___x_3495_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_3423_, 3);
                        crate::leanh::lean_dec_ref(v_post_3366_);
                        crate::leanh::lean_dec_ref(v_pre_3364_);
                        return v___x_3488_;
                    }
                }
                _ => {
                    v___x_3496_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_3364_, v_post_3366_, v___y_3423_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
                    return v___x_3496_;
                }
            },
            6 => {
                return v___x_3499_;
            }
            7 => {
                if v_isShared_3511_ == 0 {
                    v___x_3513_ = v___x_3510_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3514_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3508_);
                    v___x_3513_ = v_reuseFailAlloc_3514_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3513_;
            }
            9 => {
                if v_isShared_3519_ == 0 {
                    v___x_3521_ = v___x_3518_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3522_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3516_);
                    v___x_3521_ = v_reuseFailAlloc_3522_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3521_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___boxed(
    mut v___x_3524_: *mut crate::leanh::LeanObject,
    mut v_pre_3525_: *mut crate::leanh::LeanObject,
    mut v_e_3526_: *mut crate::leanh::LeanObject,
    mut v_post_3527_: *mut crate::leanh::LeanObject,
    mut v___y_3528_: *mut crate::leanh::LeanObject,
    mut v___y_3529_: *mut crate::leanh::LeanObject,
    mut v___y_3530_: *mut crate::leanh::LeanObject,
    mut v___y_3531_: *mut crate::leanh::LeanObject,
    mut v___y_3532_: *mut crate::leanh::LeanObject,
    mut v___y_3533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3534_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1(v___x_3524_, v_pre_3525_, v_e_3526_, v_post_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_);
    crate::leanh::lean_dec(v___y_3532_);
    crate::leanh::lean_dec_ref(v___y_3531_);
    crate::leanh::lean_dec(v___y_3530_);
    crate::leanh::lean_dec_ref(v___y_3529_);
    crate::leanh::lean_dec(v___y_3528_);
    return v_res_3534_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(
    mut v_pre_3535_: *mut crate::leanh::LeanObject,
    mut v_post_3536_: *mut crate::leanh::LeanObject,
    mut v_e_3537_: *mut crate::leanh::LeanObject,
    mut v_a_3538_: *mut crate::leanh::LeanObject,
    mut v___y_3539_: *mut crate::leanh::LeanObject,
    mut v___y_3540_: *mut crate::leanh::LeanObject,
    mut v___y_3541_: *mut crate::leanh::LeanObject,
    mut v___y_3542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3549_: u8 = 0;
    let mut v___x_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3559_: u8 = 0;
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3563_: u8 = 0;
    let mut v_unused_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3568_: u8 = 0;
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3572_: u8 = 0;
    let mut v_val_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3577_: u8 = 0;
    let mut v_a_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3581_: u8 = 0;
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3585_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_3538_);
                v___x_3544_ = crate::leanh::lean_alloc_closure(
                    l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_3544_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3544_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3544_, 2, v_a_3538_);
                v___x_3545_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0(crate::leanh::lean_box(0), v___x_3544_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_);
                if crate::leanh::lean_obj_tag(v___x_3545_) == 0 {
                    v_a_3546_ = crate::leanh::lean_ctor_get(v___x_3545_, 0);
                    v_isSharedCheck_3577_ = (!crate::leanh::lean_is_exclusive(v___x_3545_)) as u8;
                    if v_isSharedCheck_3577_ == 0 {
                        v___x_3548_ = v___x_3545_;
                        v_isShared_3549_ = v_isSharedCheck_3577_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3546_);
                        crate::leanh::lean_dec(v___x_3545_);
                        v___x_3548_ = crate::leanh::lean_box(0);
                        v_isShared_3549_ = v_isSharedCheck_3577_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_3537_);
                    crate::leanh::lean_dec_ref(v_post_3536_);
                    crate::leanh::lean_dec_ref(v_pre_3535_);
                    v_a_3578_ = crate::leanh::lean_ctor_get(v___x_3545_, 0);
                    v_isSharedCheck_3585_ = (!crate::leanh::lean_is_exclusive(v___x_3545_)) as u8;
                    if v_isSharedCheck_3585_ == 0 {
                        v___x_3580_ = v___x_3545_;
                        v_isShared_3581_ = v_isSharedCheck_3585_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3578_);
                        crate::leanh::lean_dec(v___x_3545_);
                        v___x_3580_ = crate::leanh::lean_box(0);
                        v_isShared_3581_ = v_isSharedCheck_3585_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3550_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg(v_a_3546_, v_e_3537_);
                crate::leanh::lean_dec(v_a_3546_);
                if crate::leanh::lean_obj_tag(v___x_3550_) == 0 {
                    crate::leanh::lean_del_object(v___x_3548_);
                    v___x_3551_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___closed__0;
                    crate::leanh::lean_inc_ref(v_e_3537_);
                    v___f_3552_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__1___boxed as *mut core::ffi::c_void, 10, 4);
                    crate::leanh::lean_closure_set(v___f_3552_, 0, v___x_3551_);
                    crate::leanh::lean_closure_set(v___f_3552_, 1, v_pre_3535_);
                    crate::leanh::lean_closure_set(v___f_3552_, 2, v_e_3537_);
                    crate::leanh::lean_closure_set(v___f_3552_, 3, v_post_3536_);
                    v___x_3553_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg(v___f_3552_, v_a_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_);
                    if crate::leanh::lean_obj_tag(v___x_3553_) == 0 {
                        v_a_3554_ = crate::leanh::lean_ctor_get(v___x_3553_, 0);
                        crate::leanh::lean_inc_n(v_a_3554_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_3553_, 1);
                        crate::leanh::lean_inc(v_a_3538_);
                        v___f_3555_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__2___boxed as *mut core::ffi::c_void, 4, 3);
                        crate::leanh::lean_closure_set(v___f_3555_, 0, v_a_3538_);
                        crate::leanh::lean_closure_set(v___f_3555_, 1, v_e_3537_);
                        crate::leanh::lean_closure_set(v___f_3555_, 2, v_a_3554_);
                        v___x_3556_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___lam__0(crate::leanh::lean_box(0), v___f_3555_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_);
                        if crate::leanh::lean_obj_tag(v___x_3556_) == 0 {
                            v_isSharedCheck_3563_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3556_)) as u8;
                            if v_isSharedCheck_3563_ == 0 {
                                v_unused_3564_ = crate::leanh::lean_ctor_get(v___x_3556_, 0);
                                crate::leanh::lean_dec(v_unused_3564_);
                                v___x_3558_ = v___x_3556_;
                                v_isShared_3559_ = v_isSharedCheck_3563_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_3556_);
                                v___x_3558_ = crate::leanh::lean_box(0);
                                v_isShared_3559_ = v_isSharedCheck_3563_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3554_);
                            v_a_3565_ = crate::leanh::lean_ctor_get(v___x_3556_, 0);
                            v_isSharedCheck_3572_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3556_)) as u8;
                            if v_isSharedCheck_3572_ == 0 {
                                v___x_3567_ = v___x_3556_;
                                v_isShared_3568_ = v_isSharedCheck_3572_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3565_);
                                crate::leanh::lean_dec(v___x_3556_);
                                v___x_3567_ = crate::leanh::lean_box(0);
                                v_isShared_3568_ = v_isSharedCheck_3572_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_3537_);
                        return v___x_3553_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_3537_);
                    crate::leanh::lean_dec_ref(v_post_3536_);
                    crate::leanh::lean_dec_ref(v_pre_3535_);
                    v_val_3573_ = crate::leanh::lean_ctor_get(v___x_3550_, 0);
                    crate::leanh::lean_inc(v_val_3573_);
                    crate::leanh::lean_dec_ref_known(v___x_3550_, 1);
                    if v_isShared_3549_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3548_, 0, v_val_3573_);
                        v___x_3575_ = v___x_3548_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3576_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_val_3573_);
                        v___x_3575_ = v_reuseFailAlloc_3576_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3559_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3558_, 0, v_a_3554_);
                    v___x_3561_ = v___x_3558_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3562_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3554_);
                    v___x_3561_ = v_reuseFailAlloc_3562_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3561_;
            }
            4 => {
                if v_isShared_3568_ == 0 {
                    v___x_3570_ = v___x_3567_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3571_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_a_3565_);
                    v___x_3570_ = v_reuseFailAlloc_3571_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3570_;
            }
            6 => {
                return v___x_3575_;
            }
            7 => {
                if v_isShared_3581_ == 0 {
                    v___x_3583_ = v___x_3580_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3584_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_a_3578_);
                    v___x_3583_ = v_reuseFailAlloc_3584_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3583_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(
    mut v_pre_3586_: *mut crate::leanh::LeanObject,
    mut v_post_3587_: *mut crate::leanh::LeanObject,
    mut v_e_3588_: *mut crate::leanh::LeanObject,
    mut v_a_3589_: *mut crate::leanh::LeanObject,
    mut v___y_3590_: *mut crate::leanh::LeanObject,
    mut v___y_3591_: *mut crate::leanh::LeanObject,
    mut v___y_3592_: *mut crate::leanh::LeanObject,
    mut v___y_3593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3599_: u8 = 0;
    let mut v_e_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3614_: u8 = 0;
    let mut v_a_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3618_: u8 = 0;
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3622_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_post_3587_);
                crate::leanh::lean_inc(v___y_3593_);
                crate::leanh::lean_inc_ref(v___y_3592_);
                crate::leanh::lean_inc(v___y_3591_);
                crate::leanh::lean_inc_ref(v___y_3590_);
                crate::leanh::lean_inc_ref(v_e_3588_);
                v___x_3595_ = crate::leanh::lean_apply_6(
                    v_post_3587_,
                    v_e_3588_,
                    v___y_3590_,
                    v___y_3591_,
                    v___y_3592_,
                    v___y_3593_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3595_) == 0 {
                    v_a_3596_ = crate::leanh::lean_ctor_get(v___x_3595_, 0);
                    v_isSharedCheck_3614_ = (!crate::leanh::lean_is_exclusive(v___x_3595_)) as u8;
                    if v_isSharedCheck_3614_ == 0 {
                        v___x_3598_ = v___x_3595_;
                        v_isShared_3599_ = v_isSharedCheck_3614_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3596_);
                        crate::leanh::lean_dec(v___x_3595_);
                        v___x_3598_ = crate::leanh::lean_box(0);
                        v_isShared_3599_ = v_isSharedCheck_3614_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_3588_);
                    crate::leanh::lean_dec_ref(v_post_3587_);
                    crate::leanh::lean_dec_ref(v_pre_3586_);
                    v_a_3615_ = crate::leanh::lean_ctor_get(v___x_3595_, 0);
                    v_isSharedCheck_3622_ = (!crate::leanh::lean_is_exclusive(v___x_3595_)) as u8;
                    if v_isSharedCheck_3622_ == 0 {
                        v___x_3617_ = v___x_3595_;
                        v_isShared_3618_ = v_isSharedCheck_3622_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3615_);
                        crate::leanh::lean_dec(v___x_3595_);
                        v___x_3617_ = crate::leanh::lean_box(0);
                        v_isShared_3618_ = v_isSharedCheck_3622_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => match crate::leanh::lean_obj_tag(v_a_3596_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_e_3588_);
                    crate::leanh::lean_dec_ref(v_post_3587_);
                    crate::leanh::lean_dec_ref(v_pre_3586_);
                    v_e_3600_ = crate::leanh::lean_ctor_get(v_a_3596_, 0);
                    crate::leanh::lean_inc_ref(v_e_3600_);
                    crate::leanh::lean_dec_ref_known(v_a_3596_, 1);
                    if v_isShared_3599_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3598_, 0, v_e_3600_);
                        v___x_3602_ = v___x_3598_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3603_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_e_3600_);
                        v___x_3602_ = v_reuseFailAlloc_3603_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_3598_);
                    crate::leanh::lean_dec_ref(v_e_3588_);
                    v_e_3604_ = crate::leanh::lean_ctor_get(v_a_3596_, 0);
                    crate::leanh::lean_inc_ref(v_e_3604_);
                    crate::leanh::lean_dec_ref_known(v_a_3596_, 1);
                    v___x_3605_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_3586_, v_post_3587_, v_e_3604_, v_a_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
                    return v___x_3605_;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_post_3587_);
                    crate::leanh::lean_dec_ref(v_pre_3586_);
                    v_e_x3f_3606_ = crate::leanh::lean_ctor_get(v_a_3596_, 0);
                    crate::leanh::lean_inc(v_e_x3f_3606_);
                    crate::leanh::lean_dec_ref_known(v_a_3596_, 1);
                    if crate::leanh::lean_obj_tag(v_e_x3f_3606_) == 0 {
                        if v_isShared_3599_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3598_, 0, v_e_3588_);
                            v___x_3608_ = v___x_3598_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3609_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_e_3588_);
                            v___x_3608_ = v_reuseFailAlloc_3609_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_3588_);
                        v_val_3610_ = crate::leanh::lean_ctor_get(v_e_x3f_3606_, 0);
                        crate::leanh::lean_inc(v_val_3610_);
                        crate::leanh::lean_dec_ref_known(v_e_x3f_3606_, 1);
                        if v_isShared_3599_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3598_, 0, v_val_3610_);
                            v___x_3612_ = v___x_3598_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3613_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_val_3610_);
                            v___x_3612_ = v_reuseFailAlloc_3613_;
                            state = 4;
                            continue;
                        }
                    }
                }
            },
            2 => {
                return v___x_3602_;
            }
            3 => {
                return v___x_3608_;
            }
            4 => {
                return v___x_3612_;
            }
            5 => {
                if v_isShared_3618_ == 0 {
                    v___x_3620_ = v___x_3617_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3621_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3615_);
                    v___x_3620_ = v_reuseFailAlloc_3621_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3620_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2___boxed(
    mut v_pre_3623_: *mut crate::leanh::LeanObject,
    mut v_post_3624_: *mut crate::leanh::LeanObject,
    mut v_e_3625_: *mut crate::leanh::LeanObject,
    mut v_a_3626_: *mut crate::leanh::LeanObject,
    mut v___y_3627_: *mut crate::leanh::LeanObject,
    mut v___y_3628_: *mut crate::leanh::LeanObject,
    mut v___y_3629_: *mut crate::leanh::LeanObject,
    mut v___y_3630_: *mut crate::leanh::LeanObject,
    mut v___y_3631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3632_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__2(v_pre_3623_, v_post_3624_, v_e_3625_, v_a_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
    crate::leanh::lean_dec(v___y_3630_);
    crate::leanh::lean_dec_ref(v___y_3629_);
    crate::leanh::lean_dec(v___y_3628_);
    crate::leanh::lean_dec_ref(v___y_3627_);
    crate::leanh::lean_dec(v_a_3626_);
    return v_res_3632_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1___boxed(
    mut v_pre_3633_: *mut crate::leanh::LeanObject,
    mut v_post_3634_: *mut crate::leanh::LeanObject,
    mut v_sz_3635_: *mut crate::leanh::LeanObject,
    mut v_i_3636_: *mut crate::leanh::LeanObject,
    mut v_bs_3637_: *mut crate::leanh::LeanObject,
    mut v___y_3638_: *mut crate::leanh::LeanObject,
    mut v___y_3639_: *mut crate::leanh::LeanObject,
    mut v___y_3640_: *mut crate::leanh::LeanObject,
    mut v___y_3641_: *mut crate::leanh::LeanObject,
    mut v___y_3642_: *mut crate::leanh::LeanObject,
    mut v___y_3643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3644_: usize = 0;
    let mut v_i_boxed_3645_: usize = 0;
    let mut v_res_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3644_ = crate::leanh::lean_unbox_usize(v_sz_3635_);
    crate::leanh::lean_dec(v_sz_3635_);
    v_i_boxed_3645_ = crate::leanh::lean_unbox_usize(v_i_3636_);
    crate::leanh::lean_dec(v_i_3636_);
    v_res_3646_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__1(v_pre_3633_, v_post_3634_, v_sz_boxed_3644_, v_i_boxed_3645_, v_bs_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
    crate::leanh::lean_dec(v___y_3642_);
    crate::leanh::lean_dec_ref(v___y_3641_);
    crate::leanh::lean_dec(v___y_3640_);
    crate::leanh::lean_dec_ref(v___y_3639_);
    crate::leanh::lean_dec(v___y_3638_);
    return v_res_3646_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4___boxed(
    mut v_pre_3647_: *mut crate::leanh::LeanObject,
    mut v_post_3648_: *mut crate::leanh::LeanObject,
    mut v_x_3649_: *mut crate::leanh::LeanObject,
    mut v_x_3650_: *mut crate::leanh::LeanObject,
    mut v_x_3651_: *mut crate::leanh::LeanObject,
    mut v___y_3652_: *mut crate::leanh::LeanObject,
    mut v___y_3653_: *mut crate::leanh::LeanObject,
    mut v___y_3654_: *mut crate::leanh::LeanObject,
    mut v___y_3655_: *mut crate::leanh::LeanObject,
    mut v___y_3656_: *mut crate::leanh::LeanObject,
    mut v___y_3657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3658_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__4(v_pre_3647_, v_post_3648_, v_x_3649_, v_x_3650_, v_x_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_);
    crate::leanh::lean_dec(v___y_3656_);
    crate::leanh::lean_dec_ref(v___y_3655_);
    crate::leanh::lean_dec(v___y_3654_);
    crate::leanh::lean_dec_ref(v___y_3653_);
    crate::leanh::lean_dec(v___y_3652_);
    return v_res_3658_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0___boxed(
    mut v_pre_3659_: *mut crate::leanh::LeanObject,
    mut v_post_3660_: *mut crate::leanh::LeanObject,
    mut v_e_3661_: *mut crate::leanh::LeanObject,
    mut v_a_3662_: *mut crate::leanh::LeanObject,
    mut v___y_3663_: *mut crate::leanh::LeanObject,
    mut v___y_3664_: *mut crate::leanh::LeanObject,
    mut v___y_3665_: *mut crate::leanh::LeanObject,
    mut v___y_3666_: *mut crate::leanh::LeanObject,
    mut v___y_3667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3668_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_3659_, v_post_3660_, v_e_3661_, v_a_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
    crate::leanh::lean_dec(v___y_3666_);
    crate::leanh::lean_dec_ref(v___y_3665_);
    crate::leanh::lean_dec(v___y_3664_);
    crate::leanh::lean_dec_ref(v___y_3663_);
    crate::leanh::lean_dec(v_a_3662_);
    return v_res_3668_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0(
    mut v_00_u03b1_3669_: *mut crate::leanh::LeanObject,
    mut v_x_3670_: *mut crate::leanh::LeanObject,
    mut v___y_3671_: *mut crate::leanh::LeanObject,
    mut v___y_3672_: *mut crate::leanh::LeanObject,
    mut v___y_3673_: *mut crate::leanh::LeanObject,
    mut v___y_3674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3676_ = crate::leanh::lean_apply_1(v_x_3670_, crate::leanh::lean_box(0));
    v___x_3677_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3677_, 0, v___x_3676_);
    return v___x_3677_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0___boxed(
    mut v_00_u03b1_3678_: *mut crate::leanh::LeanObject,
    mut v_x_3679_: *mut crate::leanh::LeanObject,
    mut v___y_3680_: *mut crate::leanh::LeanObject,
    mut v___y_3681_: *mut crate::leanh::LeanObject,
    mut v___y_3682_: *mut crate::leanh::LeanObject,
    mut v___y_3683_: *mut crate::leanh::LeanObject,
    mut v___y_3684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3685_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0(
        v_00_u03b1_3678_,
        v_x_3679_,
        v___y_3680_,
        v___y_3681_,
        v___y_3682_,
        v___y_3683_,
    );
    crate::leanh::lean_dec(v___y_3683_);
    crate::leanh::lean_dec_ref(v___y_3682_);
    crate::leanh::lean_dec(v___y_3681_);
    crate::leanh::lean_dec_ref(v___y_3680_);
    return v_res_3685_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3686_ = crate::leanh::lean_box(0);
    v___x_3687_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_3688_ = lean_mk_array(v___x_3687_, v___x_3686_);
    return v___x_3688_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3689_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0_once
        ),
        _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__0,
    );
    v___x_3690_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3691_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3691_, 0, v___x_3690_);
    crate::leanh::lean_ctor_set(v___x_3691_, 1, v___x_3689_);
    return v___x_3691_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3692_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1_once
        ),
        _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__1,
    );
    v___x_3693_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_3693_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3693_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3693_, 2, v___x_3692_);
    return v___x_3693_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0(
    mut v_input_3694_: *mut crate::leanh::LeanObject,
    mut v_pre_3695_: *mut crate::leanh::LeanObject,
    mut v_post_3696_: *mut crate::leanh::LeanObject,
    mut v___y_3697_: *mut crate::leanh::LeanObject,
    mut v___y_3698_: *mut crate::leanh::LeanObject,
    mut v___y_3699_: *mut crate::leanh::LeanObject,
    mut v___y_3700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3711_: u8 = 0;
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3715_: u8 = 0;
    let mut v_unused_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3702_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2_once), _init_l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___closed__2);
                v___x_3703_ =
                    l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0(
                        crate::leanh::lean_box(0),
                        v___x_3702_,
                        v___y_3697_,
                        v___y_3698_,
                        v___y_3699_,
                        v___y_3700_,
                    );
                v_a_3704_ = crate::leanh::lean_ctor_get(v___x_3703_, 0);
                crate::leanh::lean_inc(v_a_3704_);
                crate::leanh::lean_dec_ref(v___x_3703_);
                v___x_3705_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0(v_pre_3695_, v_post_3696_, v_input_3694_, v_a_3704_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
                if crate::leanh::lean_obj_tag(v___x_3705_) == 0 {
                    v_a_3706_ = crate::leanh::lean_ctor_get(v___x_3705_, 0);
                    crate::leanh::lean_inc(v_a_3706_);
                    crate::leanh::lean_dec_ref_known(v___x_3705_, 1);
                    v___x_3707_ = crate::leanh::lean_alloc_closure(
                        l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___x_3707_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_3707_, 1, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_3707_, 2, v_a_3704_);
                    v___x_3708_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___lam__0(crate::leanh::lean_box(0), v___x_3707_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
                    v_isSharedCheck_3715_ = (!crate::leanh::lean_is_exclusive(v___x_3708_)) as u8;
                    if v_isSharedCheck_3715_ == 0 {
                        v_unused_3716_ = crate::leanh::lean_ctor_get(v___x_3708_, 0);
                        crate::leanh::lean_dec(v_unused_3716_);
                        v___x_3710_ = v___x_3708_;
                        v_isShared_3711_ = v_isSharedCheck_3715_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3708_);
                        v___x_3710_ = crate::leanh::lean_box(0);
                        v_isShared_3711_ = v_isSharedCheck_3715_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3704_);
                    return v___x_3705_;
                }
            }
            1 => {
                if v_isShared_3711_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3710_, 0, v_a_3706_);
                    v___x_3713_ = v___x_3710_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3714_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3706_);
                    v___x_3713_ = v_reuseFailAlloc_3714_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3713_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0___boxed(
    mut v_input_3717_: *mut crate::leanh::LeanObject,
    mut v_pre_3718_: *mut crate::leanh::LeanObject,
    mut v_post_3719_: *mut crate::leanh::LeanObject,
    mut v___y_3720_: *mut crate::leanh::LeanObject,
    mut v___y_3721_: *mut crate::leanh::LeanObject,
    mut v___y_3722_: *mut crate::leanh::LeanObject,
    mut v___y_3723_: *mut crate::leanh::LeanObject,
    mut v___y_3724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3725_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0(
        v_input_3717_,
        v_pre_3718_,
        v_post_3719_,
        v___y_3720_,
        v___y_3721_,
        v___y_3722_,
        v___y_3723_,
    );
    crate::leanh::lean_dec(v___y_3723_);
    crate::leanh::lean_dec_ref(v___y_3722_);
    crate::leanh::lean_dec(v___y_3721_);
    crate::leanh::lean_dec_ref(v___y_3720_);
    return v_res_3725_;
}
pub unsafe fn l_Lean_Meta_PProdN_reduceProjs(
    mut v_e_3728_: *mut crate::leanh::LeanObject,
    mut v_a_3729_: *mut crate::leanh::LeanObject,
    mut v_a_3730_: *mut crate::leanh::LeanObject,
    mut v_a_3731_: *mut crate::leanh::LeanObject,
    mut v_a_3732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3734_ = l_Lean_Meta_PProdN_reduceProjs___closed__0;
    v___f_3735_ = l_Lean_Meta_PProdN_reduceProjs___closed__1;
    v___x_3736_ = l_Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0(
        v_e_3728_,
        v___f_3734_,
        v___f_3735_,
        v_a_3729_,
        v_a_3730_,
        v_a_3731_,
        v_a_3732_,
    );
    return v___x_3736_;
}
pub unsafe fn l_Lean_Meta_PProdN_reduceProjs___boxed(
    mut v_e_3737_: *mut crate::leanh::LeanObject,
    mut v_a_3738_: *mut crate::leanh::LeanObject,
    mut v_a_3739_: *mut crate::leanh::LeanObject,
    mut v_a_3740_: *mut crate::leanh::LeanObject,
    mut v_a_3741_: *mut crate::leanh::LeanObject,
    mut v_a_3742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3743_ =
        l_Lean_Meta_PProdN_reduceProjs(v_e_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_);
    crate::leanh::lean_dec(v_a_3741_);
    crate::leanh::lean_dec_ref(v_a_3740_);
    crate::leanh::lean_dec(v_a_3739_);
    crate::leanh::lean_dec_ref(v_a_3738_);
    return v_res_3743_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3(
    mut v_00_u03b2_3744_: *mut crate::leanh::LeanObject,
    mut v_m_3745_: *mut crate::leanh::LeanObject,
    mut v_a_3746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3747_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___redArg(v_m_3745_, v_a_3746_);
    return v___x_3747_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b2_3748_: *mut crate::leanh::LeanObject,
    mut v_m_3749_: *mut crate::leanh::LeanObject,
    mut v_a_3750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3751_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3(v_00_u03b2_3748_, v_m_3749_, v_a_3750_);
    crate::leanh::lean_dec_ref(v_a_3750_);
    crate::leanh::lean_dec_ref(v_m_3749_);
    return v_res_3751_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7(
    mut v_00_u03b1_3752_: *mut crate::leanh::LeanObject,
    mut v_ref_3753_: *mut crate::leanh::LeanObject,
    mut v___y_3754_: *mut crate::leanh::LeanObject,
    mut v___y_3755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3757_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_3753_);
    return v___x_3757_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7___boxed(
    mut v_00_u03b1_3758_: *mut crate::leanh::LeanObject,
    mut v_ref_3759_: *mut crate::leanh::LeanObject,
    mut v___y_3760_: *mut crate::leanh::LeanObject,
    mut v___y_3761_: *mut crate::leanh::LeanObject,
    mut v___y_3762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3763_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_3758_, v_ref_3759_, v___y_3760_, v___y_3761_);
    crate::leanh::lean_dec(v___y_3761_);
    crate::leanh::lean_dec_ref(v___y_3760_);
    return v_res_3763_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8(
    mut v_00_u03b1_3764_: *mut crate::leanh::LeanObject,
    mut v___y_3765_: *mut crate::leanh::LeanObject,
    mut v___y_3766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3768_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___redArg();
    return v___x_3768_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8___boxed(
    mut v_00_u03b1_3769_: *mut crate::leanh::LeanObject,
    mut v___y_3770_: *mut crate::leanh::LeanObject,
    mut v___y_3771_: *mut crate::leanh::LeanObject,
    mut v___y_3772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3773_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_3769_, v___y_3770_, v___y_3771_);
    crate::leanh::lean_dec(v___y_3771_);
    crate::leanh::lean_dec_ref(v___y_3770_);
    return v_res_3773_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5(
    mut v_00_u03b1_3774_: *mut crate::leanh::LeanObject,
    mut v_x_3775_: *mut crate::leanh::LeanObject,
    mut v___y_3776_: *mut crate::leanh::LeanObject,
    mut v___y_3777_: *mut crate::leanh::LeanObject,
    mut v___y_3778_: *mut crate::leanh::LeanObject,
    mut v___y_3779_: *mut crate::leanh::LeanObject,
    mut v___y_3780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3782_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___redArg(v_x_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
    return v___x_3782_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5___boxed(
    mut v_00_u03b1_3783_: *mut crate::leanh::LeanObject,
    mut v_x_3784_: *mut crate::leanh::LeanObject,
    mut v___y_3785_: *mut crate::leanh::LeanObject,
    mut v___y_3786_: *mut crate::leanh::LeanObject,
    mut v___y_3787_: *mut crate::leanh::LeanObject,
    mut v___y_3788_: *mut crate::leanh::LeanObject,
    mut v___y_3789_: *mut crate::leanh::LeanObject,
    mut v___y_3790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3791_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__5(v_00_u03b1_3783_, v_x_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_);
    crate::leanh::lean_dec(v___y_3789_);
    crate::leanh::lean_dec_ref(v___y_3788_);
    crate::leanh::lean_dec(v___y_3787_);
    crate::leanh::lean_dec_ref(v___y_3786_);
    crate::leanh::lean_dec(v___y_3785_);
    return v_res_3791_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6(
    mut v_00_u03b2_3792_: *mut crate::leanh::LeanObject,
    mut v_m_3793_: *mut crate::leanh::LeanObject,
    mut v_a_3794_: *mut crate::leanh::LeanObject,
    mut v_b_3795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3796_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6___redArg(v_m_3793_, v_a_3794_, v_b_3795_);
    return v___x_3796_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4(
    mut v_00_u03b2_3797_: *mut crate::leanh::LeanObject,
    mut v_a_3798_: *mut crate::leanh::LeanObject,
    mut v_x_3799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3800_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___redArg(v_a_3798_, v_x_3799_);
    return v___x_3800_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4___boxed(
    mut v_00_u03b2_3801_: *mut crate::leanh::LeanObject,
    mut v_a_3802_: *mut crate::leanh::LeanObject,
    mut v_x_3803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3804_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_3801_, v_a_3802_, v_x_3803_);
    crate::leanh::lean_dec(v_x_3803_);
    crate::leanh::lean_dec_ref(v_a_3802_);
    return v_res_3804_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10(
    mut v_00_u03b2_3805_: *mut crate::leanh::LeanObject,
    mut v_a_3806_: *mut crate::leanh::LeanObject,
    mut v_x_3807_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3808_: u8 = 0;
    v___x_3808_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___redArg(v_a_3806_, v_x_3807_);
    return v___x_3808_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10___boxed(
    mut v_00_u03b2_3809_: *mut crate::leanh::LeanObject,
    mut v_a_3810_: *mut crate::leanh::LeanObject,
    mut v_x_3811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3812_: u8 = 0;
    let mut v_r_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3812_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_3809_, v_a_3810_, v_x_3811_);
    crate::leanh::lean_dec(v_x_3811_);
    crate::leanh::lean_dec_ref(v_a_3810_);
    v_r_3813_ = crate::leanh::lean_box((v_res_3812_) as usize);
    return v_r_3813_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11(
    mut v_00_u03b2_3814_: *mut crate::leanh::LeanObject,
    mut v_data_3815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3816_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11___redArg(v_data_3815_);
    return v___x_3816_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__12(
    mut v_00_u03b2_3817_: *mut crate::leanh::LeanObject,
    mut v_a_3818_: *mut crate::leanh::LeanObject,
    mut v_b_3819_: *mut crate::leanh::LeanObject,
    mut v_x_3820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3821_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__12___redArg(v_a_3818_, v_b_3819_, v_x_3820_);
    return v___x_3821_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12(
    mut v_00_u03b2_3822_: *mut crate::leanh::LeanObject,
    mut v_i_3823_: *mut crate::leanh::LeanObject,
    mut v_source_3824_: *mut crate::leanh::LeanObject,
    mut v_target_3825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3826_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_3823_, v_source_3824_, v_target_3825_);
    return v___x_3826_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(
    mut v_00_u03b2_3827_: *mut crate::leanh::LeanObject,
    mut v_x_3828_: *mut crate::leanh::LeanObject,
    mut v_x_3829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3830_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_PProdN_reduceProjs_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_3828_, v_x_3829_);
    return v___x_3830_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_PProdN(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Transform(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_PProdN(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_PProdN(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Transform(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_PProdN(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_PProdN(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_PProdN(builtin);
}

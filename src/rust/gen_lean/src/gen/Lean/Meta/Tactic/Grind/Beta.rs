// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Beta
// Imports: Lean.Meta.Tactic.Grind.Types
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::l_Array_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonad___redArg, l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_beta, l_Lean_Expr_getAppFn, l_Lean_Expr_isLambda, l_Lean_mkAppN,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::AppBuilder::{l_Lean_Meta_mkCongrFun, l_Lean_Meta_mkEq};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1;
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, l_Lean_Meta_Grind_Goal_getENode,
    l_Lean_Meta_Grind_Goal_getRoot_x3f, l_Lean_Meta_Grind_addNewRawFact,
    l_Lean_Meta_Grind_getGeneration___redArg, l_Lean_Meta_Grind_getMaxGeneration___redArg,
    l_Lean_Meta_Grind_getRootENode_x3f___redArg, l_Lean_Meta_Grind_hasSameType,
    l_Lean_Meta_Grind_updateLastTag, runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Tactic::Grind::Types::lean_grind_mk_eq_proof;
static mut l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__1_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__2_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__3_value:
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
    m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__4_value:
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
    m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_getEqcLambdas___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_Meta_Grind_getEqcLambdas___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getEqcLambdas___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_getEqcLambdas___closed__1_value: crate::leanh::LeanStringObject<29> =
    crate::leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105,
            110, 100, 46, 84, 121, 112, 101, 115, 0,
        ],
    };
static mut l_Lean_Meta_Grind_getEqcLambdas___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getEqcLambdas___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_getEqcLambdas___closed__2_value: crate::leanh::LeanStringObject<24> =
    crate::leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 102, 111, 108,
            100, 69, 113, 99, 0,
        ],
    };
static mut l_Lean_Meta_Grind_getEqcLambdas___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getEqcLambdas___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_getEqcLambdas___closed__3_value: crate::leanh::LeanStringObject<34> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97,
            115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
        ],
    };
static mut l_Lean_Meta_Grind_getEqcLambdas___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getEqcLambdas___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_getEqcLambdas___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_getEqcLambdas___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [98, 101, 116, 97, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__1_value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__2_value) as *mut crate::leanh::LeanObject,2132164218978770700 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__4_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__4_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__7_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [44, 32, 117, 115, 105, 110, 103, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__9_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__10_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__9_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__10_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1365_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_1365_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1(
    mut v_msg_1370_: *mut crate::leanh::LeanObject,
    mut v___y_1371_: *mut crate::leanh::LeanObject,
    mut v___y_1372_: *mut crate::leanh::LeanObject,
    mut v___y_1373_: *mut crate::leanh::LeanObject,
    mut v___y_1374_: *mut crate::leanh::LeanObject,
    mut v___y_1375_: *mut crate::leanh::LeanObject,
    mut v___y_1376_: *mut crate::leanh::LeanObject,
    mut v___y_1377_: *mut crate::leanh::LeanObject,
    mut v___y_1378_: *mut crate::leanh::LeanObject,
    mut v___y_1379_: *mut crate::leanh::LeanObject,
    mut v___y_1380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1387_: u8 = 0;
    let mut v_toFunctor_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1394_: u8 = 0;
    let mut v___f_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1411_: u8 = 0;
    let mut v_toFunctor_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1418_: u8 = 0;
    let mut v___f_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194__overap_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1443_: u8 = 0;
    let mut v_unused_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1445_: u8 = 0;
    let mut v_unused_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1449_: u8 = 0;
    let mut v_unused_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1451_: u8 = 0;
    let mut v_unused_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1382_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__0_once
                    ),
                    _init_l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__0,
                );
                v___x_1383_ = l_StateRefT_x27_instMonad___redArg(v___x_1382_);
                v_toApplicative_1384_ = crate::leanh::lean_ctor_get(v___x_1383_, 0);
                v_isSharedCheck_1451_ = (!crate::leanh::lean_is_exclusive(v___x_1383_)) as u8;
                if v_isSharedCheck_1451_ == 0 {
                    v_unused_1452_ = crate::leanh::lean_ctor_get(v___x_1383_, 1);
                    crate::leanh::lean_dec(v_unused_1452_);
                    v___x_1386_ = v___x_1383_;
                    v_isShared_1387_ = v_isSharedCheck_1451_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_1384_);
                    crate::leanh::lean_dec(v___x_1383_);
                    v___x_1386_ = crate::leanh::lean_box(0);
                    v_isShared_1387_ = v_isSharedCheck_1451_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1388_ = crate::leanh::lean_ctor_get(v_toApplicative_1384_, 0);
                v_toSeq_1389_ = crate::leanh::lean_ctor_get(v_toApplicative_1384_, 2);
                v_toSeqLeft_1390_ = crate::leanh::lean_ctor_get(v_toApplicative_1384_, 3);
                v_toSeqRight_1391_ = crate::leanh::lean_ctor_get(v_toApplicative_1384_, 4);
                v_isSharedCheck_1449_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_1384_)) as u8;
                if v_isSharedCheck_1449_ == 0 {
                    v_unused_1450_ = crate::leanh::lean_ctor_get(v_toApplicative_1384_, 1);
                    crate::leanh::lean_dec(v_unused_1450_);
                    v___x_1393_ = v_toApplicative_1384_;
                    v_isShared_1394_ = v_isSharedCheck_1449_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_1391_);
                    crate::leanh::lean_inc(v_toSeqLeft_1390_);
                    crate::leanh::lean_inc(v_toSeq_1389_);
                    crate::leanh::lean_inc(v_toFunctor_1388_);
                    crate::leanh::lean_dec(v_toApplicative_1384_);
                    v___x_1393_ = crate::leanh::lean_box(0);
                    v_isShared_1394_ = v_isSharedCheck_1449_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1395_ = l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__1;
                v___f_1396_ = l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_1388_);
                v___f_1397_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1397_, 0, v_toFunctor_1388_);
                v___f_1398_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1398_, 0, v_toFunctor_1388_);
                v___x_1399_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1399_, 0, v___f_1397_);
                crate::leanh::lean_ctor_set(v___x_1399_, 1, v___f_1398_);
                v___f_1400_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1400_, 0, v_toSeqRight_1391_);
                v___f_1401_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1401_, 0, v_toSeqLeft_1390_);
                v___f_1402_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1402_, 0, v_toSeq_1389_);
                if v_isShared_1394_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1393_, 4, v___f_1400_);
                    crate::leanh::lean_ctor_set(v___x_1393_, 3, v___f_1401_);
                    crate::leanh::lean_ctor_set(v___x_1393_, 2, v___f_1402_);
                    crate::leanh::lean_ctor_set(v___x_1393_, 1, v___f_1395_);
                    crate::leanh::lean_ctor_set(v___x_1393_, 0, v___x_1399_);
                    v___x_1404_ = v___x_1393_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1448_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1399_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1448_, 1, v___f_1395_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1448_, 2, v___f_1402_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1448_, 3, v___f_1401_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1448_, 4, v___f_1400_);
                    v___x_1404_ = v_reuseFailAlloc_1448_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1387_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1386_, 1, v___f_1396_);
                    crate::leanh::lean_ctor_set(v___x_1386_, 0, v___x_1404_);
                    v___x_1406_ = v___x_1386_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1447_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1404_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1447_, 1, v___f_1396_);
                    v___x_1406_ = v_reuseFailAlloc_1447_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1407_ = l_StateRefT_x27_instMonad___redArg(v___x_1406_);
                v_toApplicative_1408_ = crate::leanh::lean_ctor_get(v___x_1407_, 0);
                v_isSharedCheck_1445_ = (!crate::leanh::lean_is_exclusive(v___x_1407_)) as u8;
                if v_isSharedCheck_1445_ == 0 {
                    v_unused_1446_ = crate::leanh::lean_ctor_get(v___x_1407_, 1);
                    crate::leanh::lean_dec(v_unused_1446_);
                    v___x_1410_ = v___x_1407_;
                    v_isShared_1411_ = v_isSharedCheck_1445_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_1408_);
                    crate::leanh::lean_dec(v___x_1407_);
                    v___x_1410_ = crate::leanh::lean_box(0);
                    v_isShared_1411_ = v_isSharedCheck_1445_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_1412_ = crate::leanh::lean_ctor_get(v_toApplicative_1408_, 0);
                v_toSeq_1413_ = crate::leanh::lean_ctor_get(v_toApplicative_1408_, 2);
                v_toSeqLeft_1414_ = crate::leanh::lean_ctor_get(v_toApplicative_1408_, 3);
                v_toSeqRight_1415_ = crate::leanh::lean_ctor_get(v_toApplicative_1408_, 4);
                v_isSharedCheck_1443_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_1408_)) as u8;
                if v_isSharedCheck_1443_ == 0 {
                    v_unused_1444_ = crate::leanh::lean_ctor_get(v_toApplicative_1408_, 1);
                    crate::leanh::lean_dec(v_unused_1444_);
                    v___x_1417_ = v_toApplicative_1408_;
                    v_isShared_1418_ = v_isSharedCheck_1443_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_1415_);
                    crate::leanh::lean_inc(v_toSeqLeft_1414_);
                    crate::leanh::lean_inc(v_toSeq_1413_);
                    crate::leanh::lean_inc(v_toFunctor_1412_);
                    crate::leanh::lean_dec(v_toApplicative_1408_);
                    v___x_1417_ = crate::leanh::lean_box(0);
                    v_isShared_1418_ = v_isSharedCheck_1443_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_1419_ = l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__3;
                v___f_1420_ = l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_1412_);
                v___f_1421_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1421_, 0, v_toFunctor_1412_);
                v___f_1422_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1422_, 0, v_toFunctor_1412_);
                v___x_1423_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1423_, 0, v___f_1421_);
                crate::leanh::lean_ctor_set(v___x_1423_, 1, v___f_1422_);
                v___f_1424_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1424_, 0, v_toSeqRight_1415_);
                v___f_1425_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1425_, 0, v_toSeqLeft_1414_);
                v___f_1426_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1426_, 0, v_toSeq_1413_);
                if v_isShared_1418_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1417_, 4, v___f_1424_);
                    crate::leanh::lean_ctor_set(v___x_1417_, 3, v___f_1425_);
                    crate::leanh::lean_ctor_set(v___x_1417_, 2, v___f_1426_);
                    crate::leanh::lean_ctor_set(v___x_1417_, 1, v___f_1419_);
                    crate::leanh::lean_ctor_set(v___x_1417_, 0, v___x_1423_);
                    v___x_1428_ = v___x_1417_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1442_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1423_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1442_, 1, v___f_1419_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1442_, 2, v___f_1426_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1442_, 3, v___f_1425_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1442_, 4, v___f_1424_);
                    v___x_1428_ = v_reuseFailAlloc_1442_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1411_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1410_, 1, v___f_1420_);
                    crate::leanh::lean_ctor_set(v___x_1410_, 0, v___x_1428_);
                    v___x_1430_ = v___x_1410_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1441_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1428_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1441_, 1, v___f_1420_);
                    v___x_1430_ = v_reuseFailAlloc_1441_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1431_ = l_StateRefT_x27_instMonad___redArg(v___x_1430_);
                v___x_1432_ = l_ReaderT_instMonad___redArg(v___x_1431_);
                v___x_1433_ = l_StateRefT_x27_instMonad___redArg(v___x_1432_);
                v___x_1434_ = l_ReaderT_instMonad___redArg(v___x_1433_);
                v___x_1435_ = l_ReaderT_instMonad___redArg(v___x_1434_);
                v___x_1436_ = l_StateRefT_x27_instMonad___redArg(v___x_1435_);
                v___x_1437_ = crate::leanh::lean_box(0);
                v___x_1438_ = l_instInhabitedOfMonad___redArg(v___x_1436_, v___x_1437_);
                v___x_2194__overap_1439_ = lean_panic_fn_borrowed(v___x_1438_, v_msg_1370_);
                crate::leanh::lean_dec(v___x_1438_);
                crate::leanh::lean_inc(v___y_1380_);
                crate::leanh::lean_inc_ref(v___y_1379_);
                crate::leanh::lean_inc(v___y_1378_);
                crate::leanh::lean_inc_ref(v___y_1377_);
                crate::leanh::lean_inc(v___y_1376_);
                crate::leanh::lean_inc_ref(v___y_1375_);
                crate::leanh::lean_inc(v___y_1374_);
                crate::leanh::lean_inc_ref(v___y_1373_);
                crate::leanh::lean_inc(v___y_1372_);
                crate::leanh::lean_inc(v___y_1371_);
                v___x_1440_ = crate::leanh::lean_apply_11(
                    v___x_2194__overap_1439_,
                    v___y_1371_,
                    v___y_1372_,
                    v___y_1373_,
                    v___y_1374_,
                    v___y_1375_,
                    v___y_1376_,
                    v___y_1377_,
                    v___y_1378_,
                    v___y_1379_,
                    v___y_1380_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1440_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___boxed(
    mut v_msg_1453_: *mut crate::leanh::LeanObject,
    mut v___y_1454_: *mut crate::leanh::LeanObject,
    mut v___y_1455_: *mut crate::leanh::LeanObject,
    mut v___y_1456_: *mut crate::leanh::LeanObject,
    mut v___y_1457_: *mut crate::leanh::LeanObject,
    mut v___y_1458_: *mut crate::leanh::LeanObject,
    mut v___y_1459_: *mut crate::leanh::LeanObject,
    mut v___y_1460_: *mut crate::leanh::LeanObject,
    mut v___y_1461_: *mut crate::leanh::LeanObject,
    mut v___y_1462_: *mut crate::leanh::LeanObject,
    mut v___y_1463_: *mut crate::leanh::LeanObject,
    mut v___y_1464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1465_ = l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1(
        v_msg_1453_,
        v___y_1454_,
        v___y_1455_,
        v___y_1456_,
        v___y_1457_,
        v___y_1458_,
        v___y_1459_,
        v___y_1460_,
        v___y_1461_,
        v___y_1462_,
        v___y_1463_,
    );
    crate::leanh::lean_dec(v___y_1463_);
    crate::leanh::lean_dec_ref(v___y_1462_);
    crate::leanh::lean_dec(v___y_1461_);
    crate::leanh::lean_dec_ref(v___y_1460_);
    crate::leanh::lean_dec(v___y_1459_);
    crate::leanh::lean_dec_ref(v___y_1458_);
    crate::leanh::lean_dec(v___y_1457_);
    crate::leanh::lean_dec_ref(v___y_1456_);
    crate::leanh::lean_dec(v___y_1455_);
    crate::leanh::lean_dec(v___y_1454_);
    return v_res_1465_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg(
    mut v___x_1466_: *mut crate::leanh::LeanObject,
    mut v_a_1467_: *mut crate::leanh::LeanObject,
    mut v___y_1468_: *mut crate::leanh::LeanObject,
    mut v___y_1469_: *mut crate::leanh::LeanObject,
    mut v___y_1470_: *mut crate::leanh::LeanObject,
    mut v___y_1471_: *mut crate::leanh::LeanObject,
    mut v___y_1472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1478_: u8 = 0;
    let mut v_fst_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1483_: u8 = 0;
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1488_: u8 = 0;
    let mut v_self_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_next_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: u8 = 0;
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: u8 = 0;
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1514_: u8 = 0;
    let mut v_a_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1518_: u8 = 0;
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1522_: u8 = 0;
    let mut v_isSharedCheck_1523_: u8 = 0;
    let mut v_isSharedCheck_1524_: u8 = 0;
    let mut v_unused_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1474_ = lean_st_ref_get(v___y_1468_);
                v_snd_1475_ = crate::leanh::lean_ctor_get(v_a_1467_, 1);
                v_isSharedCheck_1524_ = (!crate::leanh::lean_is_exclusive(v_a_1467_)) as u8;
                if v_isSharedCheck_1524_ == 0 {
                    v_unused_1525_ = crate::leanh::lean_ctor_get(v_a_1467_, 0);
                    crate::leanh::lean_dec(v_unused_1525_);
                    v___x_1477_ = v_a_1467_;
                    v_isShared_1478_ = v_isSharedCheck_1524_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1475_);
                    crate::leanh::lean_dec(v_a_1467_);
                    v___x_1477_ = crate::leanh::lean_box(0);
                    v_isShared_1478_ = v_isSharedCheck_1524_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_1479_ = crate::leanh::lean_ctor_get(v_snd_1475_, 0);
                v_snd_1480_ = crate::leanh::lean_ctor_get(v_snd_1475_, 1);
                v_isSharedCheck_1523_ = (!crate::leanh::lean_is_exclusive(v_snd_1475_)) as u8;
                if v_isSharedCheck_1523_ == 0 {
                    v___x_1482_ = v_snd_1475_;
                    v_isShared_1483_ = v_isSharedCheck_1523_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1480_);
                    crate::leanh::lean_inc(v_fst_1479_);
                    crate::leanh::lean_dec(v_snd_1475_);
                    v___x_1482_ = crate::leanh::lean_box(0);
                    v_isShared_1483_ = v_isSharedCheck_1523_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_fst_1479_);
                v___x_1484_ = l_Lean_Meta_Grind_Goal_getENode(
                    v___x_1474_,
                    v_fst_1479_,
                    v___y_1469_,
                    v___y_1470_,
                    v___y_1471_,
                    v___y_1472_,
                );
                crate::leanh::lean_dec(v___x_1474_);
                if crate::leanh::lean_obj_tag(v___x_1484_) == 0 {
                    v_a_1485_ = crate::leanh::lean_ctor_get(v___x_1484_, 0);
                    v_isSharedCheck_1514_ = (!crate::leanh::lean_is_exclusive(v___x_1484_)) as u8;
                    if v_isSharedCheck_1514_ == 0 {
                        v___x_1487_ = v___x_1484_;
                        v_isShared_1488_ = v_isSharedCheck_1514_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1485_);
                        crate::leanh::lean_dec(v___x_1484_);
                        v___x_1487_ = crate::leanh::lean_box(0);
                        v_isShared_1488_ = v_isSharedCheck_1514_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1482_);
                    crate::leanh::lean_dec(v_snd_1480_);
                    crate::leanh::lean_dec(v_fst_1479_);
                    crate::leanh::lean_del_object(v___x_1477_);
                    v_a_1515_ = crate::leanh::lean_ctor_get(v___x_1484_, 0);
                    v_isSharedCheck_1522_ = (!crate::leanh::lean_is_exclusive(v___x_1484_)) as u8;
                    if v_isSharedCheck_1522_ == 0 {
                        v___x_1517_ = v___x_1484_;
                        v_isShared_1518_ = v_isSharedCheck_1522_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1515_);
                        crate::leanh::lean_dec(v___x_1484_);
                        v___x_1517_ = crate::leanh::lean_box(0);
                        v_isShared_1518_ = v_isSharedCheck_1522_;
                        state = 10;
                        continue;
                    }
                }
            }
            3 => {
                v_self_1489_ = crate::leanh::lean_ctor_get(v_a_1485_, 0);
                crate::leanh::lean_inc_ref(v_self_1489_);
                v_next_1490_ = crate::leanh::lean_ctor_get(v_a_1485_, 1);
                crate::leanh::lean_inc_ref(v_next_1490_);
                crate::leanh::lean_dec(v_a_1485_);
                v___x_1491_ = crate::leanh::lean_box(0);
                v___x_1512_ = l_Lean_Expr_isLambda(v_self_1489_);
                if v___x_1512_ == 0 {
                    crate::leanh::lean_dec_ref(v_self_1489_);
                    v_a_1493_ = v_snd_1480_;
                    state = 4;
                    continue;
                } else {
                    v___x_1513_ = lean_array_push(v_snd_1480_, v_self_1489_);
                    v_a_1493_ = v___x_1513_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1494_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_next_1490_,
                        v___x_1466_,
                    );
                if v___x_1494_ == 0 {
                    crate::leanh::lean_del_object(v___x_1487_);
                    crate::leanh::lean_dec(v_fst_1479_);
                    if v_isShared_1483_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1482_, 1, v_a_1493_);
                        crate::leanh::lean_ctor_set(v___x_1482_, 0, v_next_1490_);
                        v___x_1496_ = v___x_1482_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1501_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_next_1490_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_a_1493_);
                        v___x_1496_ = v_reuseFailAlloc_1501_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_next_1490_);
                    crate::leanh::lean_inc_ref(v_a_1493_);
                    v___x_1502_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1502_, 0, v_a_1493_);
                    if v_isShared_1483_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1482_, 1, v_a_1493_);
                        v___x_1504_ = v___x_1482_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1511_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_fst_1479_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_a_1493_);
                        v___x_1504_ = v_reuseFailAlloc_1511_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_1478_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1477_, 1, v___x_1496_);
                    crate::leanh::lean_ctor_set(v___x_1477_, 0, v___x_1491_);
                    v___x_1498_ = v___x_1477_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1500_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1491_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 1, v___x_1496_);
                    v___x_1498_ = v_reuseFailAlloc_1500_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_1467_ = v___x_1498_;
                state = 0;
                continue;
            }
            7 => {
                if v_isShared_1478_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1477_, 1, v___x_1504_);
                    crate::leanh::lean_ctor_set(v___x_1477_, 0, v___x_1502_);
                    v___x_1506_ = v___x_1477_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1510_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1502_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1510_, 1, v___x_1504_);
                    v___x_1506_ = v_reuseFailAlloc_1510_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_1488_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1487_, 0, v___x_1506_);
                    v___x_1508_ = v___x_1487_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1509_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1506_);
                    v___x_1508_ = v_reuseFailAlloc_1509_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1508_;
            }
            10 => {
                if v_isShared_1518_ == 0 {
                    v___x_1520_ = v___x_1517_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1521_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1515_);
                    v___x_1520_ = v_reuseFailAlloc_1521_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1520_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg___boxed(
    mut v___x_1526_: *mut crate::leanh::LeanObject,
    mut v_a_1527_: *mut crate::leanh::LeanObject,
    mut v___y_1528_: *mut crate::leanh::LeanObject,
    mut v___y_1529_: *mut crate::leanh::LeanObject,
    mut v___y_1530_: *mut crate::leanh::LeanObject,
    mut v___y_1531_: *mut crate::leanh::LeanObject,
    mut v___y_1532_: *mut crate::leanh::LeanObject,
    mut v___y_1533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1534_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg(v___x_1526_, v_a_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
    crate::leanh::lean_dec(v___y_1532_);
    crate::leanh::lean_dec_ref(v___y_1531_);
    crate::leanh::lean_dec(v___y_1530_);
    crate::leanh::lean_dec_ref(v___y_1529_);
    crate::leanh::lean_dec(v___y_1528_);
    crate::leanh::lean_dec_ref(v___x_1526_);
    return v_res_1534_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_getEqcLambdas___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1540_ = l_Lean_Meta_Grind_getEqcLambdas___closed__3;
    v___x_1541_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1542_ = crate::leanh::lean_unsigned_to_nat(1596);
    v___x_1543_ = l_Lean_Meta_Grind_getEqcLambdas___closed__2;
    v___x_1544_ = l_Lean_Meta_Grind_getEqcLambdas___closed__1;
    v___x_1545_ = l_mkPanicMessageWithDecl(
        v___x_1544_,
        v___x_1543_,
        v___x_1542_,
        v___x_1541_,
        v___x_1540_,
    );
    return v___x_1545_;
}
pub unsafe fn l_Lean_Meta_Grind_getEqcLambdas(
    mut v_root_1546_: *mut crate::leanh::LeanObject,
    mut v_a_1547_: *mut crate::leanh::LeanObject,
    mut v_a_1548_: *mut crate::leanh::LeanObject,
    mut v_a_1549_: *mut crate::leanh::LeanObject,
    mut v_a_1550_: *mut crate::leanh::LeanObject,
    mut v_a_1551_: *mut crate::leanh::LeanObject,
    mut v_a_1552_: *mut crate::leanh::LeanObject,
    mut v_a_1553_: *mut crate::leanh::LeanObject,
    mut v_a_1554_: *mut crate::leanh::LeanObject,
    mut v_a_1555_: *mut crate::leanh::LeanObject,
    mut v_a_1556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hasLambdas_1558_: u8 = 0;
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_self_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1570_: u8 = 0;
    let mut v_fst_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1577_: u8 = 0;
    let mut v_snd_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1582_: u8 = 0;
    let mut v_unused_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1587_: u8 = 0;
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1591_: u8 = 0;
    let mut v_val_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1596_: u8 = 0;
    let mut v_a_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1600_: u8 = 0;
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1604_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_hasLambdas_1558_ = crate::leanh::lean_ctor_get_uint8(
                    v_root_1546_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 12 + 3) as u32,
                );
                if v_hasLambdas_1558_ == 0 {
                    v___x_1559_ = l_Lean_Meta_Grind_getEqcLambdas___closed__0;
                    v___x_1560_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1560_, 0, v___x_1559_);
                    return v___x_1560_;
                } else {
                    v_self_1561_ = crate::leanh::lean_ctor_get(v_root_1546_, 0);
                    v___x_1562_ = l_Lean_Meta_Grind_getEqcLambdas___closed__0;
                    v___x_1563_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_self_1561_);
                    v___x_1564_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1564_, 0, v_self_1561_);
                    crate::leanh::lean_ctor_set(v___x_1564_, 1, v___x_1562_);
                    v___x_1565_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1565_, 0, v___x_1563_);
                    crate::leanh::lean_ctor_set(v___x_1565_, 1, v___x_1564_);
                    v___x_1566_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg(v_self_1561_, v___x_1565_, v_a_1547_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_);
                    if crate::leanh::lean_obj_tag(v___x_1566_) == 0 {
                        v_a_1567_ = crate::leanh::lean_ctor_get(v___x_1566_, 0);
                        v_isSharedCheck_1596_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1566_)) as u8;
                        if v_isSharedCheck_1596_ == 0 {
                            v___x_1569_ = v___x_1566_;
                            v_isShared_1570_ = v_isSharedCheck_1596_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1567_);
                            crate::leanh::lean_dec(v___x_1566_);
                            v___x_1569_ = crate::leanh::lean_box(0);
                            v_isShared_1570_ = v_isSharedCheck_1596_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1597_ = crate::leanh::lean_ctor_get(v___x_1566_, 0);
                        v_isSharedCheck_1604_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1566_)) as u8;
                        if v_isSharedCheck_1604_ == 0 {
                            v___x_1599_ = v___x_1566_;
                            v_isShared_1600_ = v_isSharedCheck_1604_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1597_);
                            crate::leanh::lean_dec(v___x_1566_);
                            v___x_1599_ = crate::leanh::lean_box(0);
                            v_isShared_1600_ = v_isSharedCheck_1604_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_1571_ = crate::leanh::lean_ctor_get(v_a_1567_, 0);
                if crate::leanh::lean_obj_tag(v_fst_1571_) == 0 {
                    crate::leanh::lean_del_object(v___x_1569_);
                    v_snd_1572_ = crate::leanh::lean_ctor_get(v_a_1567_, 1);
                    crate::leanh::lean_inc(v_snd_1572_);
                    crate::leanh::lean_dec(v_a_1567_);
                    v___x_1573_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_getEqcLambdas___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_getEqcLambdas___closed__4_once),
                        _init_l_Lean_Meta_Grind_getEqcLambdas___closed__4,
                    );
                    v___x_1574_ = l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1(
                        v___x_1573_,
                        v_a_1547_,
                        v_a_1548_,
                        v_a_1549_,
                        v_a_1550_,
                        v_a_1551_,
                        v_a_1552_,
                        v_a_1553_,
                        v_a_1554_,
                        v_a_1555_,
                        v_a_1556_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1574_) == 0 {
                        v_isSharedCheck_1582_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1574_)) as u8;
                        if v_isSharedCheck_1582_ == 0 {
                            v_unused_1583_ = crate::leanh::lean_ctor_get(v___x_1574_, 0);
                            crate::leanh::lean_dec(v_unused_1583_);
                            v___x_1576_ = v___x_1574_;
                            v_isShared_1577_ = v_isSharedCheck_1582_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1574_);
                            v___x_1576_ = crate::leanh::lean_box(0);
                            v_isShared_1577_ = v_isSharedCheck_1582_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_snd_1572_);
                        v_a_1584_ = crate::leanh::lean_ctor_get(v___x_1574_, 0);
                        v_isSharedCheck_1591_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1574_)) as u8;
                        if v_isSharedCheck_1591_ == 0 {
                            v___x_1586_ = v___x_1574_;
                            v_isShared_1587_ = v_isSharedCheck_1591_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1584_);
                            crate::leanh::lean_dec(v___x_1574_);
                            v___x_1586_ = crate::leanh::lean_box(0);
                            v_isShared_1587_ = v_isSharedCheck_1591_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_1571_);
                    crate::leanh::lean_dec(v_a_1567_);
                    v_val_1592_ = crate::leanh::lean_ctor_get(v_fst_1571_, 0);
                    crate::leanh::lean_inc(v_val_1592_);
                    crate::leanh::lean_dec_ref_known(v_fst_1571_, 1);
                    if v_isShared_1570_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1569_, 0, v_val_1592_);
                        v___x_1594_ = v___x_1569_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1595_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_val_1592_);
                        v___x_1594_ = v_reuseFailAlloc_1595_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_1578_ = crate::leanh::lean_ctor_get(v_snd_1572_, 1);
                crate::leanh::lean_inc(v_snd_1578_);
                crate::leanh::lean_dec(v_snd_1572_);
                if v_isShared_1577_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1576_, 0, v_snd_1578_);
                    v___x_1580_ = v___x_1576_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1581_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_snd_1578_);
                    v___x_1580_ = v_reuseFailAlloc_1581_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1580_;
            }
            4 => {
                if v_isShared_1587_ == 0 {
                    v___x_1589_ = v___x_1586_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1590_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
                    v___x_1589_ = v_reuseFailAlloc_1590_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1589_;
            }
            6 => {
                return v___x_1594_;
            }
            7 => {
                if v_isShared_1600_ == 0 {
                    v___x_1602_ = v___x_1599_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1603_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
                    v___x_1602_ = v_reuseFailAlloc_1603_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1602_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_getEqcLambdas___boxed(
    mut v_root_1605_: *mut crate::leanh::LeanObject,
    mut v_a_1606_: *mut crate::leanh::LeanObject,
    mut v_a_1607_: *mut crate::leanh::LeanObject,
    mut v_a_1608_: *mut crate::leanh::LeanObject,
    mut v_a_1609_: *mut crate::leanh::LeanObject,
    mut v_a_1610_: *mut crate::leanh::LeanObject,
    mut v_a_1611_: *mut crate::leanh::LeanObject,
    mut v_a_1612_: *mut crate::leanh::LeanObject,
    mut v_a_1613_: *mut crate::leanh::LeanObject,
    mut v_a_1614_: *mut crate::leanh::LeanObject,
    mut v_a_1615_: *mut crate::leanh::LeanObject,
    mut v_a_1616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1617_ = l_Lean_Meta_Grind_getEqcLambdas(
        v_root_1605_,
        v_a_1606_,
        v_a_1607_,
        v_a_1608_,
        v_a_1609_,
        v_a_1610_,
        v_a_1611_,
        v_a_1612_,
        v_a_1613_,
        v_a_1614_,
        v_a_1615_,
    );
    crate::leanh::lean_dec(v_a_1615_);
    crate::leanh::lean_dec_ref(v_a_1614_);
    crate::leanh::lean_dec(v_a_1613_);
    crate::leanh::lean_dec_ref(v_a_1612_);
    crate::leanh::lean_dec(v_a_1611_);
    crate::leanh::lean_dec_ref(v_a_1610_);
    crate::leanh::lean_dec(v_a_1609_);
    crate::leanh::lean_dec_ref(v_a_1608_);
    crate::leanh::lean_dec(v_a_1607_);
    crate::leanh::lean_dec(v_a_1606_);
    crate::leanh::lean_dec_ref(v_root_1605_);
    return v_res_1617_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0(
    mut v___x_1618_: *mut crate::leanh::LeanObject,
    mut v_inst_1619_: *mut crate::leanh::LeanObject,
    mut v_a_1620_: *mut crate::leanh::LeanObject,
    mut v___y_1621_: *mut crate::leanh::LeanObject,
    mut v___y_1622_: *mut crate::leanh::LeanObject,
    mut v___y_1623_: *mut crate::leanh::LeanObject,
    mut v___y_1624_: *mut crate::leanh::LeanObject,
    mut v___y_1625_: *mut crate::leanh::LeanObject,
    mut v___y_1626_: *mut crate::leanh::LeanObject,
    mut v___y_1627_: *mut crate::leanh::LeanObject,
    mut v___y_1628_: *mut crate::leanh::LeanObject,
    mut v___y_1629_: *mut crate::leanh::LeanObject,
    mut v___y_1630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1632_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg(v___x_1618_, v_a_1620_, v___y_1621_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
    return v___x_1632_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___boxed(
    mut v___x_1633_: *mut crate::leanh::LeanObject,
    mut v_inst_1634_: *mut crate::leanh::LeanObject,
    mut v_a_1635_: *mut crate::leanh::LeanObject,
    mut v___y_1636_: *mut crate::leanh::LeanObject,
    mut v___y_1637_: *mut crate::leanh::LeanObject,
    mut v___y_1638_: *mut crate::leanh::LeanObject,
    mut v___y_1639_: *mut crate::leanh::LeanObject,
    mut v___y_1640_: *mut crate::leanh::LeanObject,
    mut v___y_1641_: *mut crate::leanh::LeanObject,
    mut v___y_1642_: *mut crate::leanh::LeanObject,
    mut v___y_1643_: *mut crate::leanh::LeanObject,
    mut v___y_1644_: *mut crate::leanh::LeanObject,
    mut v___y_1645_: *mut crate::leanh::LeanObject,
    mut v___y_1646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1647_ =
        l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0(
            v___x_1633_,
            v_inst_1634_,
            v_a_1635_,
            v___y_1636_,
            v___y_1637_,
            v___y_1638_,
            v___y_1639_,
            v___y_1640_,
            v___y_1641_,
            v___y_1642_,
            v___y_1643_,
            v___y_1644_,
            v___y_1645_,
        );
    crate::leanh::lean_dec(v___y_1645_);
    crate::leanh::lean_dec_ref(v___y_1644_);
    crate::leanh::lean_dec(v___y_1643_);
    crate::leanh::lean_dec_ref(v___y_1642_);
    crate::leanh::lean_dec(v___y_1641_);
    crate::leanh::lean_dec_ref(v___y_1640_);
    crate::leanh::lean_dec(v___y_1639_);
    crate::leanh::lean_dec_ref(v___y_1638_);
    crate::leanh::lean_dec(v___y_1637_);
    crate::leanh::lean_dec(v___y_1636_);
    crate::leanh::lean_dec_ref(v___x_1633_);
    return v_res_1647_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0(
    mut v___y_1651_: *mut crate::leanh::LeanObject,
    mut v_as_1652_: *mut crate::leanh::LeanObject,
    mut v_sz_1653_: usize,
    mut v_i_1654_: usize,
    mut v_b_1655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1656_: u8 = 0;
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: u8 = 0;
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: usize = 0;
    let mut v___x_1662_: usize = 0;
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1656_ = lean_usize_dec_lt(v_i_1654_, v_sz_1653_);
                if v___x_1656_ == 0 {
                    crate::leanh::lean_inc_ref(v_b_1655_);
                    return v_b_1655_;
                } else {
                    v___x_1657_ = crate::leanh::lean_box(0);
                    v_a_1658_ = lean_array_uget_borrowed(v_as_1652_, v_i_1654_);
                    v___x_1659_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_a_1658_,
                            v___y_1651_,
                        );
                    if v___x_1659_ == 0 {
                        v___x_1660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0___closed__0;
                        v___x_1661_ = 1usize;
                        v___x_1662_ = lean_usize_add(v_i_1654_, v___x_1661_);
                        v_i_1654_ = v___x_1662_;
                        v_b_1655_ = v___x_1660_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1658_);
                        v___x_1664_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1664_, 0, v_a_1658_);
                        v___x_1665_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1665_, 0, v___x_1664_);
                        v___x_1666_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1666_, 0, v___x_1665_);
                        crate::leanh::lean_ctor_set(v___x_1666_, 1, v___x_1657_);
                        return v___x_1666_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0___boxed(
    mut v___y_1667_: *mut crate::leanh::LeanObject,
    mut v_as_1668_: *mut crate::leanh::LeanObject,
    mut v_sz_1669_: *mut crate::leanh::LeanObject,
    mut v_i_1670_: *mut crate::leanh::LeanObject,
    mut v_b_1671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1672_: usize = 0;
    let mut v_i_boxed_1673_: usize = 0;
    let mut v_res_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1672_ = crate::leanh::lean_unbox_usize(v_sz_1669_);
    crate::leanh::lean_dec(v_sz_1669_);
    v_i_boxed_1673_ = crate::leanh::lean_unbox_usize(v_i_1670_);
    crate::leanh::lean_dec(v_i_1670_);
    v_res_1674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0(v___y_1667_, v_as_1668_, v_sz_boxed_1672_, v_i_boxed_1673_, v_b_1671_);
    crate::leanh::lean_dec_ref(v_b_1671_);
    crate::leanh::lean_dec_ref(v_as_1668_);
    crate::leanh::lean_dec_ref(v___y_1667_);
    return v_res_1674_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg(
    mut v_e_1678_: *mut crate::leanh::LeanObject,
    mut v_a_1679_: *mut crate::leanh::LeanObject,
    mut v___y_1680_: *mut crate::leanh::LeanObject,
    mut v___y_1681_: *mut crate::leanh::LeanObject,
    mut v___y_1682_: *mut crate::leanh::LeanObject,
    mut v___y_1683_: *mut crate::leanh::LeanObject,
    mut v___y_1684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1690_: u8 = 0;
    let mut v_fst_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1695_: u8 = 0;
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1700_: u8 = 0;
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_self_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_next_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: u8 = 0;
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1731_: usize = 0;
    let mut v___x_1732_: usize = 0;
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1739_: u8 = 0;
    let mut v_a_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1743_: u8 = 0;
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1747_: u8 = 0;
    let mut v_isSharedCheck_1748_: u8 = 0;
    let mut v_isSharedCheck_1749_: u8 = 0;
    let mut v_unused_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1686_ = lean_st_ref_get(v___y_1680_);
                v_snd_1687_ = crate::leanh::lean_ctor_get(v_a_1679_, 1);
                v_isSharedCheck_1749_ = (!crate::leanh::lean_is_exclusive(v_a_1679_)) as u8;
                if v_isSharedCheck_1749_ == 0 {
                    v_unused_1750_ = crate::leanh::lean_ctor_get(v_a_1679_, 0);
                    crate::leanh::lean_dec(v_unused_1750_);
                    v___x_1689_ = v_a_1679_;
                    v_isShared_1690_ = v_isSharedCheck_1749_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1687_);
                    crate::leanh::lean_dec(v_a_1679_);
                    v___x_1689_ = crate::leanh::lean_box(0);
                    v_isShared_1690_ = v_isSharedCheck_1749_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_1691_ = crate::leanh::lean_ctor_get(v_snd_1687_, 0);
                v_snd_1692_ = crate::leanh::lean_ctor_get(v_snd_1687_, 1);
                v_isSharedCheck_1748_ = (!crate::leanh::lean_is_exclusive(v_snd_1687_)) as u8;
                if v_isSharedCheck_1748_ == 0 {
                    v___x_1694_ = v_snd_1687_;
                    v_isShared_1695_ = v_isSharedCheck_1748_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1692_);
                    crate::leanh::lean_inc(v_fst_1691_);
                    crate::leanh::lean_dec(v_snd_1687_);
                    v___x_1694_ = crate::leanh::lean_box(0);
                    v_isShared_1695_ = v_isSharedCheck_1748_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_fst_1691_);
                v___x_1696_ = l_Lean_Meta_Grind_Goal_getENode(
                    v___x_1686_,
                    v_fst_1691_,
                    v___y_1681_,
                    v___y_1682_,
                    v___y_1683_,
                    v___y_1684_,
                );
                crate::leanh::lean_dec(v___x_1686_);
                if crate::leanh::lean_obj_tag(v___x_1696_) == 0 {
                    v_a_1697_ = crate::leanh::lean_ctor_get(v___x_1696_, 0);
                    v_isSharedCheck_1739_ = (!crate::leanh::lean_is_exclusive(v___x_1696_)) as u8;
                    if v_isSharedCheck_1739_ == 0 {
                        v___x_1699_ = v___x_1696_;
                        v_isShared_1700_ = v_isSharedCheck_1739_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1697_);
                        crate::leanh::lean_dec(v___x_1696_);
                        v___x_1699_ = crate::leanh::lean_box(0);
                        v_isShared_1700_ = v_isSharedCheck_1739_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1694_);
                    crate::leanh::lean_dec(v_snd_1692_);
                    crate::leanh::lean_dec(v_fst_1691_);
                    crate::leanh::lean_del_object(v___x_1689_);
                    v_a_1740_ = crate::leanh::lean_ctor_get(v___x_1696_, 0);
                    v_isSharedCheck_1747_ = (!crate::leanh::lean_is_exclusive(v___x_1696_)) as u8;
                    if v_isSharedCheck_1747_ == 0 {
                        v___x_1742_ = v___x_1696_;
                        v_isShared_1743_ = v_isSharedCheck_1747_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1740_);
                        crate::leanh::lean_dec(v___x_1696_);
                        v___x_1742_ = crate::leanh::lean_box(0);
                        v_isShared_1743_ = v_isSharedCheck_1747_;
                        state = 12;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1701_ = lean_st_ref_get(v___y_1680_);
                v_self_1702_ = crate::leanh::lean_ctor_get(v_a_1697_, 0);
                crate::leanh::lean_inc_ref(v_self_1702_);
                v_next_1703_ = crate::leanh::lean_ctor_get(v_a_1697_, 1);
                crate::leanh::lean_inc_ref(v_next_1703_);
                crate::leanh::lean_dec(v_a_1697_);
                v___x_1704_ = crate::leanh::lean_box(0);
                v_fn_1736_ = l_Lean_Expr_getAppFn(v_self_1702_);
                crate::leanh::lean_dec_ref(v_self_1702_);
                v___x_1737_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v___x_1701_, v_fn_1736_);
                crate::leanh::lean_dec(v___x_1701_);
                if crate::leanh::lean_obj_tag(v___x_1737_) == 0 {
                    v___y_1729_ = v_fn_1736_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_fn_1736_);
                    v_val_1738_ = crate::leanh::lean_ctor_get(v___x_1737_, 0);
                    crate::leanh::lean_inc(v_val_1738_);
                    crate::leanh::lean_dec_ref_known(v___x_1737_, 1);
                    v___y_1729_ = v_val_1738_;
                    state = 11;
                    continue;
                }
            }
            4 => {
                v___x_1707_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_next_1703_,
                        v_e_1678_,
                    );
                if v___x_1707_ == 0 {
                    crate::leanh::lean_del_object(v___x_1699_);
                    crate::leanh::lean_dec(v_fst_1691_);
                    if v_isShared_1695_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1694_, 1, v_a_1706_);
                        crate::leanh::lean_ctor_set(v___x_1694_, 0, v_next_1703_);
                        v___x_1709_ = v___x_1694_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1714_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_next_1703_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1714_, 1, v_a_1706_);
                        v___x_1709_ = v_reuseFailAlloc_1714_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_next_1703_);
                    crate::leanh::lean_inc_ref(v_a_1706_);
                    v___x_1715_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1715_, 0, v_a_1706_);
                    if v_isShared_1695_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1694_, 1, v_a_1706_);
                        v___x_1717_ = v___x_1694_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1724_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_fst_1691_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1724_, 1, v_a_1706_);
                        v___x_1717_ = v_reuseFailAlloc_1724_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_1690_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1689_, 1, v___x_1709_);
                    crate::leanh::lean_ctor_set(v___x_1689_, 0, v___x_1704_);
                    v___x_1711_ = v___x_1689_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1713_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1704_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1713_, 1, v___x_1709_);
                    v___x_1711_ = v_reuseFailAlloc_1713_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_1679_ = v___x_1711_;
                state = 0;
                continue;
            }
            7 => {
                if v_isShared_1690_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1689_, 1, v___x_1717_);
                    crate::leanh::lean_ctor_set(v___x_1689_, 0, v___x_1715_);
                    v___x_1719_ = v___x_1689_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1723_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1715_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1723_, 1, v___x_1717_);
                    v___x_1719_ = v_reuseFailAlloc_1723_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_1700_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1699_, 0, v___x_1719_);
                    v___x_1721_ = v___x_1699_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1722_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1719_);
                    v___x_1721_ = v_reuseFailAlloc_1722_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1721_;
            }
            10 => {
                v___x_1727_ = lean_array_push(v_snd_1692_, v___y_1726_);
                v_a_1706_ = v___x_1727_;
                state = 4;
                continue;
            }
            11 => {
                v___x_1730_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg___closed__0;
                v_sz_1731_ = lean_array_size(v_snd_1692_);
                v___x_1732_ = 0usize;
                v___x_1733_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0(v___y_1729_, v_snd_1692_, v_sz_1731_, v___x_1732_, v___x_1730_);
                v_fst_1734_ = crate::leanh::lean_ctor_get(v___x_1733_, 0);
                crate::leanh::lean_inc(v_fst_1734_);
                crate::leanh::lean_dec_ref(v___x_1733_);
                if crate::leanh::lean_obj_tag(v_fst_1734_) == 0 {
                    v___y_1726_ = v___y_1729_;
                    state = 10;
                    continue;
                } else {
                    v_val_1735_ = crate::leanh::lean_ctor_get(v_fst_1734_, 0);
                    crate::leanh::lean_inc(v_val_1735_);
                    crate::leanh::lean_dec_ref_known(v_fst_1734_, 1);
                    if crate::leanh::lean_obj_tag(v_val_1735_) == 0 {
                        v___y_1726_ = v___y_1729_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_val_1735_, 1);
                        crate::leanh::lean_dec_ref(v___y_1729_);
                        v_a_1706_ = v_snd_1692_;
                        state = 4;
                        continue;
                    }
                }
            }
            12 => {
                if v_isShared_1743_ == 0 {
                    v___x_1745_ = v___x_1742_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1746_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
                    v___x_1745_ = v_reuseFailAlloc_1746_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1745_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg___boxed(
    mut v_e_1751_: *mut crate::leanh::LeanObject,
    mut v_a_1752_: *mut crate::leanh::LeanObject,
    mut v___y_1753_: *mut crate::leanh::LeanObject,
    mut v___y_1754_: *mut crate::leanh::LeanObject,
    mut v___y_1755_: *mut crate::leanh::LeanObject,
    mut v___y_1756_: *mut crate::leanh::LeanObject,
    mut v___y_1757_: *mut crate::leanh::LeanObject,
    mut v___y_1758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1759_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg(v_e_1751_, v_a_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
    crate::leanh::lean_dec(v___y_1757_);
    crate::leanh::lean_dec_ref(v___y_1756_);
    crate::leanh::lean_dec(v___y_1755_);
    crate::leanh::lean_dec_ref(v___y_1754_);
    crate::leanh::lean_dec(v___y_1753_);
    crate::leanh::lean_dec_ref(v_e_1751_);
    return v_res_1759_;
}
pub unsafe fn l_Lean_Meta_Grind_getFnRoots(
    mut v_e_1760_: *mut crate::leanh::LeanObject,
    mut v_a_1761_: *mut crate::leanh::LeanObject,
    mut v_a_1762_: *mut crate::leanh::LeanObject,
    mut v_a_1763_: *mut crate::leanh::LeanObject,
    mut v_a_1764_: *mut crate::leanh::LeanObject,
    mut v_a_1765_: *mut crate::leanh::LeanObject,
    mut v_a_1766_: *mut crate::leanh::LeanObject,
    mut v_a_1767_: *mut crate::leanh::LeanObject,
    mut v_a_1768_: *mut crate::leanh::LeanObject,
    mut v_a_1769_: *mut crate::leanh::LeanObject,
    mut v_a_1770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1780_: u8 = 0;
    let mut v_fst_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1787_: u8 = 0;
    let mut v_snd_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1792_: u8 = 0;
    let mut v_unused_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1797_: u8 = 0;
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1801_: u8 = 0;
    let mut v_val_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1806_: u8 = 0;
    let mut v_a_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1810_: u8 = 0;
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1814_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1772_ = l_Lean_Meta_Grind_getEqcLambdas___closed__0;
                v___x_1773_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_e_1760_);
                v___x_1774_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1774_, 0, v_e_1760_);
                crate::leanh::lean_ctor_set(v___x_1774_, 1, v___x_1772_);
                v___x_1775_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1775_, 0, v___x_1773_);
                crate::leanh::lean_ctor_set(v___x_1775_, 1, v___x_1774_);
                v___x_1776_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg(v_e_1760_, v___x_1775_, v_a_1761_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_);
                crate::leanh::lean_dec_ref(v_e_1760_);
                if crate::leanh::lean_obj_tag(v___x_1776_) == 0 {
                    v_a_1777_ = crate::leanh::lean_ctor_get(v___x_1776_, 0);
                    v_isSharedCheck_1806_ = (!crate::leanh::lean_is_exclusive(v___x_1776_)) as u8;
                    if v_isSharedCheck_1806_ == 0 {
                        v___x_1779_ = v___x_1776_;
                        v_isShared_1780_ = v_isSharedCheck_1806_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1777_);
                        crate::leanh::lean_dec(v___x_1776_);
                        v___x_1779_ = crate::leanh::lean_box(0);
                        v_isShared_1780_ = v_isSharedCheck_1806_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1807_ = crate::leanh::lean_ctor_get(v___x_1776_, 0);
                    v_isSharedCheck_1814_ = (!crate::leanh::lean_is_exclusive(v___x_1776_)) as u8;
                    if v_isSharedCheck_1814_ == 0 {
                        v___x_1809_ = v___x_1776_;
                        v_isShared_1810_ = v_isSharedCheck_1814_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1807_);
                        crate::leanh::lean_dec(v___x_1776_);
                        v___x_1809_ = crate::leanh::lean_box(0);
                        v_isShared_1810_ = v_isSharedCheck_1814_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1781_ = crate::leanh::lean_ctor_get(v_a_1777_, 0);
                if crate::leanh::lean_obj_tag(v_fst_1781_) == 0 {
                    crate::leanh::lean_del_object(v___x_1779_);
                    v_snd_1782_ = crate::leanh::lean_ctor_get(v_a_1777_, 1);
                    crate::leanh::lean_inc(v_snd_1782_);
                    crate::leanh::lean_dec(v_a_1777_);
                    v___x_1783_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_getEqcLambdas___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_getEqcLambdas___closed__4_once),
                        _init_l_Lean_Meta_Grind_getEqcLambdas___closed__4,
                    );
                    v___x_1784_ = l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1(
                        v___x_1783_,
                        v_a_1761_,
                        v_a_1762_,
                        v_a_1763_,
                        v_a_1764_,
                        v_a_1765_,
                        v_a_1766_,
                        v_a_1767_,
                        v_a_1768_,
                        v_a_1769_,
                        v_a_1770_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1784_) == 0 {
                        v_isSharedCheck_1792_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1784_)) as u8;
                        if v_isSharedCheck_1792_ == 0 {
                            v_unused_1793_ = crate::leanh::lean_ctor_get(v___x_1784_, 0);
                            crate::leanh::lean_dec(v_unused_1793_);
                            v___x_1786_ = v___x_1784_;
                            v_isShared_1787_ = v_isSharedCheck_1792_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1784_);
                            v___x_1786_ = crate::leanh::lean_box(0);
                            v_isShared_1787_ = v_isSharedCheck_1792_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_snd_1782_);
                        v_a_1794_ = crate::leanh::lean_ctor_get(v___x_1784_, 0);
                        v_isSharedCheck_1801_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1784_)) as u8;
                        if v_isSharedCheck_1801_ == 0 {
                            v___x_1796_ = v___x_1784_;
                            v_isShared_1797_ = v_isSharedCheck_1801_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1794_);
                            crate::leanh::lean_dec(v___x_1784_);
                            v___x_1796_ = crate::leanh::lean_box(0);
                            v_isShared_1797_ = v_isSharedCheck_1801_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_1781_);
                    crate::leanh::lean_dec(v_a_1777_);
                    v_val_1802_ = crate::leanh::lean_ctor_get(v_fst_1781_, 0);
                    crate::leanh::lean_inc(v_val_1802_);
                    crate::leanh::lean_dec_ref_known(v_fst_1781_, 1);
                    if v_isShared_1780_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1779_, 0, v_val_1802_);
                        v___x_1804_ = v___x_1779_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1805_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_val_1802_);
                        v___x_1804_ = v_reuseFailAlloc_1805_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_1788_ = crate::leanh::lean_ctor_get(v_snd_1782_, 1);
                crate::leanh::lean_inc(v_snd_1788_);
                crate::leanh::lean_dec(v_snd_1782_);
                if v_isShared_1787_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1786_, 0, v_snd_1788_);
                    v___x_1790_ = v___x_1786_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1791_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_snd_1788_);
                    v___x_1790_ = v_reuseFailAlloc_1791_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1790_;
            }
            4 => {
                if v_isShared_1797_ == 0 {
                    v___x_1799_ = v___x_1796_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1800_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
                    v___x_1799_ = v_reuseFailAlloc_1800_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1799_;
            }
            6 => {
                return v___x_1804_;
            }
            7 => {
                if v_isShared_1810_ == 0 {
                    v___x_1812_ = v___x_1809_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1813_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
                    v___x_1812_ = v_reuseFailAlloc_1813_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1812_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_getFnRoots___boxed(
    mut v_e_1815_: *mut crate::leanh::LeanObject,
    mut v_a_1816_: *mut crate::leanh::LeanObject,
    mut v_a_1817_: *mut crate::leanh::LeanObject,
    mut v_a_1818_: *mut crate::leanh::LeanObject,
    mut v_a_1819_: *mut crate::leanh::LeanObject,
    mut v_a_1820_: *mut crate::leanh::LeanObject,
    mut v_a_1821_: *mut crate::leanh::LeanObject,
    mut v_a_1822_: *mut crate::leanh::LeanObject,
    mut v_a_1823_: *mut crate::leanh::LeanObject,
    mut v_a_1824_: *mut crate::leanh::LeanObject,
    mut v_a_1825_: *mut crate::leanh::LeanObject,
    mut v_a_1826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1827_ = l_Lean_Meta_Grind_getFnRoots(
        v_e_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_,
        v_a_1823_, v_a_1824_, v_a_1825_,
    );
    crate::leanh::lean_dec(v_a_1825_);
    crate::leanh::lean_dec_ref(v_a_1824_);
    crate::leanh::lean_dec(v_a_1823_);
    crate::leanh::lean_dec_ref(v_a_1822_);
    crate::leanh::lean_dec(v_a_1821_);
    crate::leanh::lean_dec_ref(v_a_1820_);
    crate::leanh::lean_dec(v_a_1819_);
    crate::leanh::lean_dec_ref(v_a_1818_);
    crate::leanh::lean_dec(v_a_1817_);
    crate::leanh::lean_dec(v_a_1816_);
    return v_res_1827_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1(
    mut v_e_1828_: *mut crate::leanh::LeanObject,
    mut v_inst_1829_: *mut crate::leanh::LeanObject,
    mut v_a_1830_: *mut crate::leanh::LeanObject,
    mut v___y_1831_: *mut crate::leanh::LeanObject,
    mut v___y_1832_: *mut crate::leanh::LeanObject,
    mut v___y_1833_: *mut crate::leanh::LeanObject,
    mut v___y_1834_: *mut crate::leanh::LeanObject,
    mut v___y_1835_: *mut crate::leanh::LeanObject,
    mut v___y_1836_: *mut crate::leanh::LeanObject,
    mut v___y_1837_: *mut crate::leanh::LeanObject,
    mut v___y_1838_: *mut crate::leanh::LeanObject,
    mut v___y_1839_: *mut crate::leanh::LeanObject,
    mut v___y_1840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1842_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg(v_e_1828_, v_a_1830_, v___y_1831_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
    return v___x_1842_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___boxed(
    mut v_e_1843_: *mut crate::leanh::LeanObject,
    mut v_inst_1844_: *mut crate::leanh::LeanObject,
    mut v_a_1845_: *mut crate::leanh::LeanObject,
    mut v___y_1846_: *mut crate::leanh::LeanObject,
    mut v___y_1847_: *mut crate::leanh::LeanObject,
    mut v___y_1848_: *mut crate::leanh::LeanObject,
    mut v___y_1849_: *mut crate::leanh::LeanObject,
    mut v___y_1850_: *mut crate::leanh::LeanObject,
    mut v___y_1851_: *mut crate::leanh::LeanObject,
    mut v___y_1852_: *mut crate::leanh::LeanObject,
    mut v___y_1853_: *mut crate::leanh::LeanObject,
    mut v___y_1854_: *mut crate::leanh::LeanObject,
    mut v___y_1855_: *mut crate::leanh::LeanObject,
    mut v___y_1856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1857_ =
        l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1(
            v_e_1843_,
            v_inst_1844_,
            v_a_1845_,
            v___y_1846_,
            v___y_1847_,
            v___y_1848_,
            v___y_1849_,
            v___y_1850_,
            v___y_1851_,
            v___y_1852_,
            v___y_1853_,
            v___y_1854_,
            v___y_1855_,
        );
    crate::leanh::lean_dec(v___y_1855_);
    crate::leanh::lean_dec_ref(v___y_1854_);
    crate::leanh::lean_dec(v___y_1853_);
    crate::leanh::lean_dec_ref(v___y_1852_);
    crate::leanh::lean_dec(v___y_1851_);
    crate::leanh::lean_dec_ref(v___y_1850_);
    crate::leanh::lean_dec(v___y_1849_);
    crate::leanh::lean_dec_ref(v___y_1848_);
    crate::leanh::lean_dec(v___y_1847_);
    crate::leanh::lean_dec(v___y_1846_);
    crate::leanh::lean_dec_ref(v_e_1843_);
    return v_res_1857_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg(
    mut v_as_1858_: *mut crate::leanh::LeanObject,
    mut v_i_1859_: usize,
    mut v_stop_1860_: usize,
    mut v_b_1861_: *mut crate::leanh::LeanObject,
    mut v___y_1862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: usize = 0;
    let mut v___x_1867_: usize = 0;
    let mut v___y_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: u8 = 0;
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: u8 = 0;
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1872_ = lean_usize_dec_eq(v_i_1859_, v_stop_1860_);
                if v___x_1872_ == 0 {
                    v___x_1873_ = lean_array_uget_borrowed(v_as_1858_, v_i_1859_);
                    v___x_1874_ =
                        l_Lean_Meta_Grind_getGeneration___redArg(v___x_1873_, v___y_1862_);
                    if crate::leanh::lean_obj_tag(v___x_1874_) == 0 {
                        v_a_1875_ = crate::leanh::lean_ctor_get(v___x_1874_, 0);
                        crate::leanh::lean_inc(v_a_1875_);
                        v___x_1876_ = lean_nat_dec_le(v_b_1861_, v_a_1875_);
                        crate::leanh::lean_dec(v_a_1875_);
                        if v___x_1876_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_1874_, 1);
                            v_a_1865_ = v_b_1861_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_b_1861_);
                            v___y_1870_ = v___x_1874_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_b_1861_);
                        v___y_1870_ = v___x_1874_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1877_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1877_, 0, v_b_1861_);
                    return v___x_1877_;
                }
            }
            1 => {
                v___x_1866_ = 1usize;
                v___x_1867_ = lean_usize_add(v_i_1859_, v___x_1866_);
                v_i_1859_ = v___x_1867_;
                v_b_1861_ = v_a_1865_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_1870_) == 0 {
                    v_a_1871_ = crate::leanh::lean_ctor_get(v___y_1870_, 0);
                    crate::leanh::lean_inc(v_a_1871_);
                    crate::leanh::lean_dec_ref_known(v___y_1870_, 1);
                    v_a_1865_ = v_a_1871_;
                    state = 1;
                    continue;
                } else {
                    return v___y_1870_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg___boxed(
    mut v_as_1878_: *mut crate::leanh::LeanObject,
    mut v_i_1879_: *mut crate::leanh::LeanObject,
    mut v_stop_1880_: *mut crate::leanh::LeanObject,
    mut v_b_1881_: *mut crate::leanh::LeanObject,
    mut v___y_1882_: *mut crate::leanh::LeanObject,
    mut v___y_1883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1884_: usize = 0;
    let mut v_stop_boxed_1885_: usize = 0;
    let mut v_res_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1884_ = crate::leanh::lean_unbox_usize(v_i_1879_);
    crate::leanh::lean_dec(v_i_1879_);
    v_stop_boxed_1885_ = crate::leanh::lean_unbox_usize(v_stop_1880_);
    crate::leanh::lean_dec(v_stop_1880_);
    v_res_1886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg(v_as_1878_, v_i_boxed_1884_, v_stop_boxed_1885_, v_b_1881_, v___y_1882_);
    crate::leanh::lean_dec(v___y_1882_);
    crate::leanh::lean_dec_ref(v_as_1878_);
    return v_res_1886_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1_spec__1(
    mut v_msgData_1887_: *mut crate::leanh::LeanObject,
    mut v___y_1888_: *mut crate::leanh::LeanObject,
    mut v___y_1889_: *mut crate::leanh::LeanObject,
    mut v___y_1890_: *mut crate::leanh::LeanObject,
    mut v___y_1891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1893_ = lean_st_ref_get(v___y_1891_);
    v_env_1894_ = crate::leanh::lean_ctor_get(v___x_1893_, 0);
    crate::leanh::lean_inc_ref(v_env_1894_);
    crate::leanh::lean_dec(v___x_1893_);
    v___x_1895_ = lean_st_ref_get(v___y_1889_);
    v_mctx_1896_ = crate::leanh::lean_ctor_get(v___x_1895_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1896_);
    crate::leanh::lean_dec(v___x_1895_);
    v_lctx_1897_ = crate::leanh::lean_ctor_get(v___y_1888_, 2);
    v_options_1898_ = crate::leanh::lean_ctor_get(v___y_1890_, 2);
    crate::leanh::lean_inc_ref(v_options_1898_);
    crate::leanh::lean_inc_ref(v_lctx_1897_);
    v___x_1899_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1899_, 0, v_env_1894_);
    crate::leanh::lean_ctor_set(v___x_1899_, 1, v_mctx_1896_);
    crate::leanh::lean_ctor_set(v___x_1899_, 2, v_lctx_1897_);
    crate::leanh::lean_ctor_set(v___x_1899_, 3, v_options_1898_);
    v___x_1900_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1900_, 0, v___x_1899_);
    crate::leanh::lean_ctor_set(v___x_1900_, 1, v_msgData_1887_);
    v___x_1901_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1901_, 0, v___x_1900_);
    return v___x_1901_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1_spec__1___boxed(
    mut v_msgData_1902_: *mut crate::leanh::LeanObject,
    mut v___y_1903_: *mut crate::leanh::LeanObject,
    mut v___y_1904_: *mut crate::leanh::LeanObject,
    mut v___y_1905_: *mut crate::leanh::LeanObject,
    mut v___y_1906_: *mut crate::leanh::LeanObject,
    mut v___y_1907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1908_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1_spec__1(v_msgData_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
    crate::leanh::lean_dec(v___y_1906_);
    crate::leanh::lean_dec_ref(v___y_1905_);
    crate::leanh::lean_dec(v___y_1904_);
    crate::leanh::lean_dec_ref(v___y_1903_);
    return v_res_1908_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0()
-> f64 {
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: f64 = 0.0;
    v___x_1909_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1910_ = lean_float_of_nat(v___x_1909_);
    return v___x_1910_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg(
    mut v_cls_1914_: *mut crate::leanh::LeanObject,
    mut v_msg_1915_: *mut crate::leanh::LeanObject,
    mut v___y_1916_: *mut crate::leanh::LeanObject,
    mut v___y_1917_: *mut crate::leanh::LeanObject,
    mut v___y_1918_: *mut crate::leanh::LeanObject,
    mut v___y_1919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1926_: u8 = 0;
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1939_: u8 = 0;
    let mut v_tid_1940_: u64 = 0;
    let mut v_traces_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1944_: u8 = 0;
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: f64 = 0.0;
    let mut v___x_1947_: u8 = 0;
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1965_: u8 = 0;
    let mut v_isSharedCheck_1966_: u8 = 0;
    let mut v_isSharedCheck_1967_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1921_ = crate::leanh::lean_ctor_get(v___y_1918_, 5);
                v___x_1922_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1_spec__1(v_msg_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
                v_a_1923_ = crate::leanh::lean_ctor_get(v___x_1922_, 0);
                v_isSharedCheck_1967_ = (!crate::leanh::lean_is_exclusive(v___x_1922_)) as u8;
                if v_isSharedCheck_1967_ == 0 {
                    v___x_1925_ = v___x_1922_;
                    v_isShared_1926_ = v_isSharedCheck_1967_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1923_);
                    crate::leanh::lean_dec(v___x_1922_);
                    v___x_1925_ = crate::leanh::lean_box(0);
                    v_isShared_1926_ = v_isSharedCheck_1967_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1927_ = lean_st_ref_take(v___y_1919_);
                v_traceState_1928_ = crate::leanh::lean_ctor_get(v___x_1927_, 4);
                v_env_1929_ = crate::leanh::lean_ctor_get(v___x_1927_, 0);
                v_nextMacroScope_1930_ = crate::leanh::lean_ctor_get(v___x_1927_, 1);
                v_ngen_1931_ = crate::leanh::lean_ctor_get(v___x_1927_, 2);
                v_auxDeclNGen_1932_ = crate::leanh::lean_ctor_get(v___x_1927_, 3);
                v_cache_1933_ = crate::leanh::lean_ctor_get(v___x_1927_, 5);
                v_messages_1934_ = crate::leanh::lean_ctor_get(v___x_1927_, 6);
                v_infoState_1935_ = crate::leanh::lean_ctor_get(v___x_1927_, 7);
                v_snapshotTasks_1936_ = crate::leanh::lean_ctor_get(v___x_1927_, 8);
                v_isSharedCheck_1966_ = (!crate::leanh::lean_is_exclusive(v___x_1927_)) as u8;
                if v_isSharedCheck_1966_ == 0 {
                    v___x_1938_ = v___x_1927_;
                    v_isShared_1939_ = v_isSharedCheck_1966_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1936_);
                    crate::leanh::lean_inc(v_infoState_1935_);
                    crate::leanh::lean_inc(v_messages_1934_);
                    crate::leanh::lean_inc(v_cache_1933_);
                    crate::leanh::lean_inc(v_traceState_1928_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1932_);
                    crate::leanh::lean_inc(v_ngen_1931_);
                    crate::leanh::lean_inc(v_nextMacroScope_1930_);
                    crate::leanh::lean_inc(v_env_1929_);
                    crate::leanh::lean_dec(v___x_1927_);
                    v___x_1938_ = crate::leanh::lean_box(0);
                    v_isShared_1939_ = v_isSharedCheck_1966_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_1940_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_1928_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_1941_ = crate::leanh::lean_ctor_get(v_traceState_1928_, 0);
                v_isSharedCheck_1965_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_1928_)) as u8;
                if v_isSharedCheck_1965_ == 0 {
                    v___x_1943_ = v_traceState_1928_;
                    v_isShared_1944_ = v_isSharedCheck_1965_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_1941_);
                    crate::leanh::lean_dec(v_traceState_1928_);
                    v___x_1943_ = crate::leanh::lean_box(0);
                    v_isShared_1944_ = v_isSharedCheck_1965_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1945_ = crate::leanh::lean_box(0);
                v___x_1946_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0);
                v___x_1947_ = 0;
                v___x_1948_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__1;
                v___x_1949_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_1949_, 0, v_cls_1914_);
                crate::leanh::lean_ctor_set(v___x_1949_, 1, v___x_1945_);
                crate::leanh::lean_ctor_set(v___x_1949_, 2, v___x_1948_);
                crate::leanh::lean_ctor_set_float(
                    v___x_1949_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_1946_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_1949_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_1946_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1949_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_1947_,
                );
                v___x_1950_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__2;
                v___x_1951_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1951_, 0, v___x_1949_);
                crate::leanh::lean_ctor_set(v___x_1951_, 1, v_a_1923_);
                crate::leanh::lean_ctor_set(v___x_1951_, 2, v___x_1950_);
                crate::leanh::lean_inc(v_ref_1921_);
                v___x_1952_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1952_, 0, v_ref_1921_);
                crate::leanh::lean_ctor_set(v___x_1952_, 1, v___x_1951_);
                v___x_1953_ = l_Lean_PersistentArray_push___redArg(v_traces_1941_, v___x_1952_);
                if v_isShared_1944_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1943_, 0, v___x_1953_);
                    v___x_1955_ = v___x_1943_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1964_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1953_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_1964_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_1940_,
                    );
                    v___x_1955_ = v_reuseFailAlloc_1964_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1939_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1938_, 4, v___x_1955_);
                    v___x_1957_ = v___x_1938_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1963_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_env_1929_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1963_, 1, v_nextMacroScope_1930_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1963_, 2, v_ngen_1931_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1963_, 3, v_auxDeclNGen_1932_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1963_, 4, v___x_1955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1963_, 5, v_cache_1933_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1963_, 6, v_messages_1934_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1963_, 7, v_infoState_1935_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1963_, 8, v_snapshotTasks_1936_);
                    v___x_1957_ = v_reuseFailAlloc_1963_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1958_ = lean_st_ref_set(v___y_1919_, v___x_1957_);
                v___x_1959_ = crate::leanh::lean_box(0);
                if v_isShared_1926_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1925_, 0, v___x_1959_);
                    v___x_1961_ = v___x_1925_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1962_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___x_1959_);
                    v___x_1961_ = v_reuseFailAlloc_1962_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1961_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___boxed(
    mut v_cls_1968_: *mut crate::leanh::LeanObject,
    mut v_msg_1969_: *mut crate::leanh::LeanObject,
    mut v___y_1970_: *mut crate::leanh::LeanObject,
    mut v___y_1971_: *mut crate::leanh::LeanObject,
    mut v___y_1972_: *mut crate::leanh::LeanObject,
    mut v___y_1973_: *mut crate::leanh::LeanObject,
    mut v___y_1974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1975_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg(
        v_cls_1968_,
        v_msg_1969_,
        v___y_1970_,
        v___y_1971_,
        v___y_1972_,
        v___y_1973_,
    );
    crate::leanh::lean_dec(v___y_1973_);
    crate::leanh::lean_dec_ref(v___y_1972_);
    crate::leanh::lean_dec(v___y_1971_);
    crate::leanh::lean_dec_ref(v___y_1970_);
    return v_res_1975_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(
    mut v_as_1976_: *mut crate::leanh::LeanObject,
    mut v_sz_1977_: usize,
    mut v_i_1978_: usize,
    mut v_b_1979_: *mut crate::leanh::LeanObject,
    mut v___y_1980_: *mut crate::leanh::LeanObject,
    mut v___y_1981_: *mut crate::leanh::LeanObject,
    mut v___y_1982_: *mut crate::leanh::LeanObject,
    mut v___y_1983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1985_: u8 = 0;
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: usize = 0;
    let mut v___x_1991_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1985_ = lean_usize_dec_lt(v_i_1978_, v_sz_1977_);
                if v___x_1985_ == 0 {
                    v___x_1986_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1986_, 0, v_b_1979_);
                    return v___x_1986_;
                } else {
                    v_a_1987_ = lean_array_uget_borrowed(v_as_1976_, v_i_1978_);
                    crate::leanh::lean_inc(v_a_1987_);
                    v___x_1988_ = l_Lean_Meta_mkCongrFun(
                        v_b_1979_,
                        v_a_1987_,
                        v___y_1980_,
                        v___y_1981_,
                        v___y_1982_,
                        v___y_1983_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1988_) == 0 {
                        v_a_1989_ = crate::leanh::lean_ctor_get(v___x_1988_, 0);
                        crate::leanh::lean_inc(v_a_1989_);
                        crate::leanh::lean_dec_ref_known(v___x_1988_, 1);
                        v___x_1990_ = 1usize;
                        v___x_1991_ = lean_usize_add(v_i_1978_, v___x_1990_);
                        v_i_1978_ = v___x_1991_;
                        v_b_1979_ = v_a_1989_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1988_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg___boxed(
    mut v_as_1993_: *mut crate::leanh::LeanObject,
    mut v_sz_1994_: *mut crate::leanh::LeanObject,
    mut v_i_1995_: *mut crate::leanh::LeanObject,
    mut v_b_1996_: *mut crate::leanh::LeanObject,
    mut v___y_1997_: *mut crate::leanh::LeanObject,
    mut v___y_1998_: *mut crate::leanh::LeanObject,
    mut v___y_1999_: *mut crate::leanh::LeanObject,
    mut v___y_2000_: *mut crate::leanh::LeanObject,
    mut v___y_2001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2002_: usize = 0;
    let mut v_i_boxed_2003_: usize = 0;
    let mut v_res_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2002_ = crate::leanh::lean_unbox_usize(v_sz_1994_);
    crate::leanh::lean_dec(v_sz_1994_);
    v_i_boxed_2003_ = crate::leanh::lean_unbox_usize(v_i_1995_);
    crate::leanh::lean_dec(v_i_1995_);
    v_res_2004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(v_as_1993_, v_sz_boxed_2002_, v_i_boxed_2003_, v_b_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
    crate::leanh::lean_dec(v___y_2000_);
    crate::leanh::lean_dec_ref(v___y_1999_);
    crate::leanh::lean_dec(v___y_1998_);
    crate::leanh::lean_dec_ref(v___y_1997_);
    crate::leanh::lean_dec_ref(v_as_1993_);
    return v_res_2004_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2016_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__3;
    v___x_2017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__5;
    v___x_2018_ = l_Lean_Name_append(v___x_2017_, v___x_2016_);
    return v___x_2018_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__7;
    v___x_2021_ = l_Lean_stringToMessageData(v___x_2020_);
    return v___x_2021_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3(
    mut v_args_2027_: *mut crate::leanh::LeanObject,
    mut v_f_2028_: *mut crate::leanh::LeanObject,
    mut v_as_2029_: *mut crate::leanh::LeanObject,
    mut v_sz_2030_: usize,
    mut v_i_2031_: usize,
    mut v_b_2032_: *mut crate::leanh::LeanObject,
    mut v___y_2033_: *mut crate::leanh::LeanObject,
    mut v___y_2034_: *mut crate::leanh::LeanObject,
    mut v___y_2035_: *mut crate::leanh::LeanObject,
    mut v___y_2036_: *mut crate::leanh::LeanObject,
    mut v___y_2037_: *mut crate::leanh::LeanObject,
    mut v___y_2038_: *mut crate::leanh::LeanObject,
    mut v___y_2039_: *mut crate::leanh::LeanObject,
    mut v___y_2040_: *mut crate::leanh::LeanObject,
    mut v___y_2041_: *mut crate::leanh::LeanObject,
    mut v___y_2042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: usize = 0;
    let mut v___x_2047_: usize = 0;
    let mut v___x_2049_: u8 = 0;
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2073_: u8 = 0;
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2077_: u8 = 0;
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2085_: u8 = 0;
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: u8 = 0;
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: u8 = 0;
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2095_: usize = 0;
    let mut v___x_2096_: usize = 0;
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2101_: u8 = 0;
    let mut v_a_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: u8 = 0;
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2118_: u8 = 0;
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2122_: u8 = 0;
    let mut v_a_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2126_: u8 = 0;
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2130_: u8 = 0;
    let mut v_a_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2134_: u8 = 0;
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2138_: u8 = 0;
    let mut v_a_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2142_: u8 = 0;
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2146_: u8 = 0;
    let mut v_a_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2150_: u8 = 0;
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2154_: u8 = 0;
    let mut v_a_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2158_: u8 = 0;
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2162_: u8 = 0;
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2167_: u8 = 0;
    let mut v_a_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2171_: u8 = 0;
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2175_: u8 = 0;
    let mut v___y_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2182_: u8 = 0;
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2186_: u8 = 0;
    let mut v___x_2187_: u8 = 0;
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: u8 = 0;
    let mut v___x_2197_: u8 = 0;
    let mut v___x_2198_: usize = 0;
    let mut v___x_2199_: usize = 0;
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: usize = 0;
    let mut v___x_2202_: usize = 0;
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: u8 = 0;
    let mut v_a_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2208_: u8 = 0;
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2212_: u8 = 0;
    let mut v_a_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2216_: u8 = 0;
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2220_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2049_ = lean_usize_dec_lt(v_i_2031_, v_sz_2030_);
                if v___x_2049_ == 0 {
                    crate::leanh::lean_dec_ref(v_f_2028_);
                    crate::leanh::lean_dec_ref(v_args_2027_);
                    v___x_2050_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2050_, 0, v_b_2032_);
                    return v___x_2050_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_2032_);
                    v___x_2051_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__0;
                    v_a_2052_ = lean_array_uget_borrowed(v_as_2029_, v_i_2031_);
                    crate::leanh::lean_inc_ref(v_args_2027_);
                    crate::leanh::lean_inc(v_a_2052_);
                    v___x_2078_ = l_Lean_Expr_beta(v_a_2052_, v_args_2027_);
                    v___x_2187_ = l_Lean_Expr_isLambda(v___x_2078_);
                    if v___x_2187_ == 0 {
                        v___x_2188_ =
                            l_Lean_Meta_Grind_getGeneration___redArg(v_a_2052_, v___y_2033_);
                        if crate::leanh::lean_obj_tag(v___x_2188_) == 0 {
                            v_a_2189_ = crate::leanh::lean_ctor_get(v___x_2188_, 0);
                            crate::leanh::lean_inc(v_a_2189_);
                            crate::leanh::lean_dec_ref_known(v___x_2188_, 1);
                            v___x_2190_ =
                                l_Lean_Meta_Grind_getGeneration___redArg(v_f_2028_, v___y_2033_);
                            if crate::leanh::lean_obj_tag(v___x_2190_) == 0 {
                                v_a_2191_ = crate::leanh::lean_ctor_get(v___x_2190_, 0);
                                crate::leanh::lean_inc(v_a_2191_);
                                crate::leanh::lean_dec_ref_known(v___x_2190_, 1);
                                v___x_2204_ = lean_nat_dec_le(v_a_2189_, v_a_2191_);
                                if v___x_2204_ == 0 {
                                    crate::leanh::lean_dec(v_a_2191_);
                                    v___y_2193_ = v_a_2189_;
                                    state = 25;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_2189_);
                                    v___y_2193_ = v_a_2191_;
                                    state = 25;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2189_);
                                crate::leanh::lean_dec_ref(v___x_2078_);
                                crate::leanh::lean_dec_ref(v_f_2028_);
                                crate::leanh::lean_dec_ref(v_args_2027_);
                                v_a_2205_ = crate::leanh::lean_ctor_get(v___x_2190_, 0);
                                v_isSharedCheck_2212_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2190_)) as u8;
                                if v_isSharedCheck_2212_ == 0 {
                                    v___x_2207_ = v___x_2190_;
                                    v_isShared_2208_ = v_isSharedCheck_2212_;
                                    state = 26;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2205_);
                                    crate::leanh::lean_dec(v___x_2190_);
                                    v___x_2207_ = crate::leanh::lean_box(0);
                                    v_isShared_2208_ = v_isSharedCheck_2212_;
                                    state = 26;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2078_);
                            crate::leanh::lean_dec_ref(v_f_2028_);
                            crate::leanh::lean_dec_ref(v_args_2027_);
                            v_a_2213_ = crate::leanh::lean_ctor_get(v___x_2188_, 0);
                            v_isSharedCheck_2220_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2188_)) as u8;
                            if v_isSharedCheck_2220_ == 0 {
                                v___x_2215_ = v___x_2188_;
                                v_isShared_2216_ = v_isSharedCheck_2220_;
                                state = 28;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2213_);
                                crate::leanh::lean_dec(v___x_2188_);
                                v___x_2215_ = crate::leanh::lean_box(0);
                                v_isShared_2216_ = v_isSharedCheck_2220_;
                                state = 28;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2078_);
                        v_a_2045_ = v___x_2051_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2046_ = 1usize;
                v___x_2047_ = lean_usize_add(v_i_2031_, v___x_2046_);
                crate::leanh::lean_inc_ref(v_a_2045_);
                v_i_2031_ = v___x_2047_;
                v_b_2032_ = v_a_2045_;
                state = 0;
                continue;
            }
            2 => {
                crate::leanh::lean_inc(v_a_2052_);
                v___x_2067_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2067_, 0, v_a_2052_);
                v___x_2068_ = crate::leanh::lean_box(1);
                v___x_2069_ = l_Lean_Meta_Grind_addNewRawFact(
                    v___y_2054_,
                    v___y_2055_,
                    v___y_2056_,
                    v___x_2067_,
                    v___x_2068_,
                    v___y_2057_,
                    v___y_2058_,
                    v___y_2059_,
                    v___y_2060_,
                    v___y_2061_,
                    v___y_2062_,
                    v___y_2063_,
                    v___y_2064_,
                    v___y_2065_,
                    v___y_2066_,
                );
                if crate::leanh::lean_obj_tag(v___x_2069_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2069_, 1);
                    v_a_2045_ = v___x_2051_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_f_2028_);
                    crate::leanh::lean_dec_ref(v_args_2027_);
                    v_a_2070_ = crate::leanh::lean_ctor_get(v___x_2069_, 0);
                    v_isSharedCheck_2077_ = (!crate::leanh::lean_is_exclusive(v___x_2069_)) as u8;
                    if v_isSharedCheck_2077_ == 0 {
                        v___x_2072_ = v___x_2069_;
                        v_isShared_2073_ = v_isSharedCheck_2077_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2070_);
                        crate::leanh::lean_dec(v___x_2069_);
                        v___x_2072_ = crate::leanh::lean_box(0);
                        v_isShared_2073_ = v_isSharedCheck_2077_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2073_ == 0 {
                    v___x_2075_ = v___x_2072_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2076_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
                    v___x_2075_ = v_reuseFailAlloc_2076_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2075_;
            }
            5 => {
                v___x_2081_ = l_Lean_Meta_Grind_getMaxGeneration___redArg(v___y_2035_);
                if crate::leanh::lean_obj_tag(v___x_2081_) == 0 {
                    v_a_2082_ = crate::leanh::lean_ctor_get(v___x_2081_, 0);
                    v_isSharedCheck_2167_ = (!crate::leanh::lean_is_exclusive(v___x_2081_)) as u8;
                    if v_isSharedCheck_2167_ == 0 {
                        v___x_2084_ = v___x_2081_;
                        v_isShared_2085_ = v_isSharedCheck_2167_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2082_);
                        crate::leanh::lean_dec(v___x_2081_);
                        v___x_2084_ = crate::leanh::lean_box(0);
                        v_isShared_2085_ = v_isSharedCheck_2167_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2080_);
                    crate::leanh::lean_dec_ref(v___x_2078_);
                    crate::leanh::lean_dec_ref(v_f_2028_);
                    crate::leanh::lean_dec_ref(v_args_2027_);
                    v_a_2168_ = crate::leanh::lean_ctor_get(v___x_2081_, 0);
                    v_isSharedCheck_2175_ = (!crate::leanh::lean_is_exclusive(v___x_2081_)) as u8;
                    if v_isSharedCheck_2175_ == 0 {
                        v___x_2170_ = v___x_2081_;
                        v_isShared_2171_ = v_isSharedCheck_2175_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2168_);
                        crate::leanh::lean_dec(v___x_2081_);
                        v___x_2170_ = crate::leanh::lean_box(0);
                        v_isShared_2171_ = v_isSharedCheck_2175_;
                        state = 20;
                        continue;
                    }
                }
            }
            6 => {
                v___x_2086_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2087_ = lean_nat_add(v_a_2080_, v___x_2086_);
                crate::leanh::lean_dec(v_a_2080_);
                v___x_2088_ = lean_nat_dec_le(v_a_2082_, v___x_2087_);
                crate::leanh::lean_dec(v_a_2082_);
                if v___x_2088_ == 0 {
                    crate::leanh::lean_del_object(v___x_2084_);
                    crate::leanh::lean_inc_ref_n(v_f_2028_, 2);
                    v___x_2089_ = l_Lean_mkAppN(v_f_2028_, v_args_2027_);
                    crate::leanh::lean_inc(v_a_2052_);
                    v___x_2090_ = l_Lean_Meta_Grind_hasSameType(
                        v_f_2028_,
                        v_a_2052_,
                        v___y_2039_,
                        v___y_2040_,
                        v___y_2041_,
                        v___y_2042_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2090_) == 0 {
                        v_a_2091_ = crate::leanh::lean_ctor_get(v___x_2090_, 0);
                        crate::leanh::lean_inc(v_a_2091_);
                        crate::leanh::lean_dec_ref_known(v___x_2090_, 1);
                        v___x_2092_ = (crate::leanh::lean_unbox(v_a_2091_) as u8);
                        crate::leanh::lean_dec(v_a_2091_);
                        if v___x_2092_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2089_);
                            crate::leanh::lean_dec(v___x_2087_);
                            crate::leanh::lean_dec_ref(v___x_2078_);
                            v_a_2045_ = v___x_2051_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v___y_2042_);
                            crate::leanh::lean_inc_ref(v___y_2041_);
                            crate::leanh::lean_inc(v___y_2040_);
                            crate::leanh::lean_inc_ref(v___y_2039_);
                            crate::leanh::lean_inc(v___y_2038_);
                            crate::leanh::lean_inc_ref(v___y_2037_);
                            crate::leanh::lean_inc(v___y_2036_);
                            crate::leanh::lean_inc_ref(v___y_2035_);
                            crate::leanh::lean_inc(v___y_2034_);
                            crate::leanh::lean_inc(v___y_2033_);
                            crate::leanh::lean_inc(v_a_2052_);
                            crate::leanh::lean_inc_ref(v_f_2028_);
                            v___x_2093_ = lean_grind_mk_eq_proof(
                                v_f_2028_,
                                v_a_2052_,
                                v___y_2033_,
                                v___y_2034_,
                                v___y_2035_,
                                v___y_2036_,
                                v___y_2037_,
                                v___y_2038_,
                                v___y_2039_,
                                v___y_2040_,
                                v___y_2041_,
                                v___y_2042_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2093_) == 0 {
                                v_a_2094_ = crate::leanh::lean_ctor_get(v___x_2093_, 0);
                                crate::leanh::lean_inc(v_a_2094_);
                                crate::leanh::lean_dec_ref_known(v___x_2093_, 1);
                                v_sz_2095_ = lean_array_size(v_args_2027_);
                                v___x_2096_ = 0usize;
                                v___x_2097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(v_args_2027_, v_sz_2095_, v___x_2096_, v_a_2094_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
                                if crate::leanh::lean_obj_tag(v___x_2097_) == 0 {
                                    v_a_2098_ = crate::leanh::lean_ctor_get(v___x_2097_, 0);
                                    crate::leanh::lean_inc(v_a_2098_);
                                    crate::leanh::lean_dec_ref_known(v___x_2097_, 1);
                                    v___x_2099_ = l_Lean_Meta_mkEq(
                                        v___x_2089_,
                                        v___x_2078_,
                                        v___y_2039_,
                                        v___y_2040_,
                                        v___y_2041_,
                                        v___y_2042_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2099_) == 0 {
                                        v_options_2100_ =
                                            crate::leanh::lean_ctor_get(v___y_2041_, 2);
                                        v_hasTrace_2101_ = crate::leanh::lean_ctor_get_uint8(
                                            v_options_2100_,
                                            (core::mem::size_of::<*mut crate::leanh::LeanObject>()
                                                * 1)
                                                as u32,
                                        );
                                        if v_hasTrace_2101_ == 0 {
                                            v_a_2102_ = crate::leanh::lean_ctor_get(v___x_2099_, 0);
                                            crate::leanh::lean_inc(v_a_2102_);
                                            crate::leanh::lean_dec_ref_known(v___x_2099_, 1);
                                            v___y_2054_ = v_a_2098_;
                                            v___y_2055_ = v_a_2102_;
                                            v___y_2056_ = v___x_2087_;
                                            v___y_2057_ = v___y_2033_;
                                            v___y_2058_ = v___y_2034_;
                                            v___y_2059_ = v___y_2035_;
                                            v___y_2060_ = v___y_2036_;
                                            v___y_2061_ = v___y_2037_;
                                            v___y_2062_ = v___y_2038_;
                                            v___y_2063_ = v___y_2039_;
                                            v___y_2064_ = v___y_2040_;
                                            v___y_2065_ = v___y_2041_;
                                            v___y_2066_ = v___y_2042_;
                                            state = 2;
                                            continue;
                                        } else {
                                            v_a_2103_ = crate::leanh::lean_ctor_get(v___x_2099_, 0);
                                            crate::leanh::lean_inc(v_a_2103_);
                                            crate::leanh::lean_dec_ref_known(v___x_2099_, 1);
                                            v_inheritedTraceOptions_2104_ =
                                                crate::leanh::lean_ctor_get(v___y_2041_, 13);
                                            v___x_2105_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__3;
                                            v___x_2106_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__6_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__6);
                                            v___x_2107_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2104_, v_options_2100_, v___x_2106_);
                                            if v___x_2107_ == 0 {
                                                v___y_2054_ = v_a_2098_;
                                                v___y_2055_ = v_a_2103_;
                                                v___y_2056_ = v___x_2087_;
                                                v___y_2057_ = v___y_2033_;
                                                v___y_2058_ = v___y_2034_;
                                                v___y_2059_ = v___y_2035_;
                                                v___y_2060_ = v___y_2036_;
                                                v___y_2061_ = v___y_2037_;
                                                v___y_2062_ = v___y_2038_;
                                                v___y_2063_ = v___y_2039_;
                                                v___y_2064_ = v___y_2040_;
                                                v___y_2065_ = v___y_2041_;
                                                v___y_2066_ = v___y_2042_;
                                                state = 2;
                                                continue;
                                            } else {
                                                v___x_2108_ = l_Lean_Meta_Grind_updateLastTag(
                                                    v___y_2033_,
                                                    v___y_2034_,
                                                    v___y_2035_,
                                                    v___y_2036_,
                                                    v___y_2037_,
                                                    v___y_2038_,
                                                    v___y_2039_,
                                                    v___y_2040_,
                                                    v___y_2041_,
                                                    v___y_2042_,
                                                );
                                                if crate::leanh::lean_obj_tag(v___x_2108_) == 0 {
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_2108_,
                                                        1,
                                                    );
                                                    crate::leanh::lean_inc(v_a_2103_);
                                                    v___x_2109_ =
                                                        l_Lean_MessageData_ofExpr(v_a_2103_);
                                                    v___x_2110_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__8);
                                                    v___x_2111_ = crate::leanh::lean_alloc_ctor(
                                                        7,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2111_,
                                                        0,
                                                        v___x_2109_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2111_,
                                                        1,
                                                        v___x_2110_,
                                                    );
                                                    crate::leanh::lean_inc(v_a_2052_);
                                                    v___x_2112_ =
                                                        l_Lean_MessageData_ofExpr(v_a_2052_);
                                                    v___x_2113_ = crate::leanh::lean_alloc_ctor(
                                                        7,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2113_,
                                                        0,
                                                        v___x_2111_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2113_,
                                                        1,
                                                        v___x_2112_,
                                                    );
                                                    v___x_2114_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg(v___x_2105_, v___x_2113_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
                                                    if crate::leanh::lean_obj_tag(v___x_2114_) == 0
                                                    {
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_2114_,
                                                            1,
                                                        );
                                                        v___y_2054_ = v_a_2098_;
                                                        v___y_2055_ = v_a_2103_;
                                                        v___y_2056_ = v___x_2087_;
                                                        v___y_2057_ = v___y_2033_;
                                                        v___y_2058_ = v___y_2034_;
                                                        v___y_2059_ = v___y_2035_;
                                                        v___y_2060_ = v___y_2036_;
                                                        v___y_2061_ = v___y_2037_;
                                                        v___y_2062_ = v___y_2038_;
                                                        v___y_2063_ = v___y_2039_;
                                                        v___y_2064_ = v___y_2040_;
                                                        v___y_2065_ = v___y_2041_;
                                                        v___y_2066_ = v___y_2042_;
                                                        state = 2;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_dec(v_a_2103_);
                                                        crate::leanh::lean_dec(v_a_2098_);
                                                        crate::leanh::lean_dec(v___x_2087_);
                                                        crate::leanh::lean_dec_ref(v_f_2028_);
                                                        crate::leanh::lean_dec_ref(v_args_2027_);
                                                        v_a_2115_ = crate::leanh::lean_ctor_get(
                                                            v___x_2114_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_2122_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_2114_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_2122_ == 0 {
                                                            v___x_2117_ = v___x_2114_;
                                                            v_isShared_2118_ =
                                                                v_isSharedCheck_2122_;
                                                            state = 7;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_2115_);
                                                            crate::leanh::lean_dec(v___x_2114_);
                                                            v___x_2117_ = crate::leanh::lean_box(0);
                                                            v_isShared_2118_ =
                                                                v_isSharedCheck_2122_;
                                                            state = 7;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v_a_2103_);
                                                    crate::leanh::lean_dec(v_a_2098_);
                                                    crate::leanh::lean_dec(v___x_2087_);
                                                    crate::leanh::lean_dec_ref(v_f_2028_);
                                                    crate::leanh::lean_dec_ref(v_args_2027_);
                                                    v_a_2123_ =
                                                        crate::leanh::lean_ctor_get(v___x_2108_, 0);
                                                    v_isSharedCheck_2130_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_2108_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_2130_ == 0 {
                                                        v___x_2125_ = v___x_2108_;
                                                        v_isShared_2126_ = v_isSharedCheck_2130_;
                                                        state = 9;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_2123_);
                                                        crate::leanh::lean_dec(v___x_2108_);
                                                        v___x_2125_ = crate::leanh::lean_box(0);
                                                        v_isShared_2126_ = v_isSharedCheck_2130_;
                                                        state = 9;
                                                        continue;
                                                    }
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_2098_);
                                        crate::leanh::lean_dec(v___x_2087_);
                                        crate::leanh::lean_dec_ref(v_f_2028_);
                                        crate::leanh::lean_dec_ref(v_args_2027_);
                                        v_a_2131_ = crate::leanh::lean_ctor_get(v___x_2099_, 0);
                                        v_isSharedCheck_2138_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2099_)) as u8;
                                        if v_isSharedCheck_2138_ == 0 {
                                            v___x_2133_ = v___x_2099_;
                                            v_isShared_2134_ = v_isSharedCheck_2138_;
                                            state = 11;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2131_);
                                            crate::leanh::lean_dec(v___x_2099_);
                                            v___x_2133_ = crate::leanh::lean_box(0);
                                            v_isShared_2134_ = v_isSharedCheck_2138_;
                                            state = 11;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_2089_);
                                    crate::leanh::lean_dec(v___x_2087_);
                                    crate::leanh::lean_dec_ref(v___x_2078_);
                                    crate::leanh::lean_dec_ref(v_f_2028_);
                                    crate::leanh::lean_dec_ref(v_args_2027_);
                                    v_a_2139_ = crate::leanh::lean_ctor_get(v___x_2097_, 0);
                                    v_isSharedCheck_2146_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2097_)) as u8;
                                    if v_isSharedCheck_2146_ == 0 {
                                        v___x_2141_ = v___x_2097_;
                                        v_isShared_2142_ = v_isSharedCheck_2146_;
                                        state = 13;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2139_);
                                        crate::leanh::lean_dec(v___x_2097_);
                                        v___x_2141_ = crate::leanh::lean_box(0);
                                        v_isShared_2142_ = v_isSharedCheck_2146_;
                                        state = 13;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_2089_);
                                crate::leanh::lean_dec(v___x_2087_);
                                crate::leanh::lean_dec_ref(v___x_2078_);
                                crate::leanh::lean_dec_ref(v_f_2028_);
                                crate::leanh::lean_dec_ref(v_args_2027_);
                                v_a_2147_ = crate::leanh::lean_ctor_get(v___x_2093_, 0);
                                v_isSharedCheck_2154_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2093_)) as u8;
                                if v_isSharedCheck_2154_ == 0 {
                                    v___x_2149_ = v___x_2093_;
                                    v_isShared_2150_ = v_isSharedCheck_2154_;
                                    state = 15;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2147_);
                                    crate::leanh::lean_dec(v___x_2093_);
                                    v___x_2149_ = crate::leanh::lean_box(0);
                                    v_isShared_2150_ = v_isSharedCheck_2154_;
                                    state = 15;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2089_);
                        crate::leanh::lean_dec(v___x_2087_);
                        crate::leanh::lean_dec_ref(v___x_2078_);
                        crate::leanh::lean_dec_ref(v_f_2028_);
                        crate::leanh::lean_dec_ref(v_args_2027_);
                        v_a_2155_ = crate::leanh::lean_ctor_get(v___x_2090_, 0);
                        v_isSharedCheck_2162_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2090_)) as u8;
                        if v_isSharedCheck_2162_ == 0 {
                            v___x_2157_ = v___x_2090_;
                            v_isShared_2158_ = v_isSharedCheck_2162_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2155_);
                            crate::leanh::lean_dec(v___x_2090_);
                            v___x_2157_ = crate::leanh::lean_box(0);
                            v_isShared_2158_ = v_isSharedCheck_2162_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2087_);
                    crate::leanh::lean_dec_ref(v___x_2078_);
                    crate::leanh::lean_dec_ref(v_f_2028_);
                    crate::leanh::lean_dec_ref(v_args_2027_);
                    v___x_2163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__10;
                    if v_isShared_2085_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2084_, 0, v___x_2163_);
                        v___x_2165_ = v___x_2084_;
                        state = 19;
                        continue;
                    } else {
                        v_reuseFailAlloc_2166_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2163_);
                        v___x_2165_ = v_reuseFailAlloc_2166_;
                        state = 19;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_2118_ == 0 {
                    v___x_2120_ = v___x_2117_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2121_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2115_);
                    v___x_2120_ = v_reuseFailAlloc_2121_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2120_;
            }
            9 => {
                if v_isShared_2126_ == 0 {
                    v___x_2128_ = v___x_2125_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2129_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2123_);
                    v___x_2128_ = v_reuseFailAlloc_2129_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2128_;
            }
            11 => {
                if v_isShared_2134_ == 0 {
                    v___x_2136_ = v___x_2133_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2137_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2131_);
                    v___x_2136_ = v_reuseFailAlloc_2137_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2136_;
            }
            13 => {
                if v_isShared_2142_ == 0 {
                    v___x_2144_ = v___x_2141_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2145_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
                    v___x_2144_ = v_reuseFailAlloc_2145_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2144_;
            }
            15 => {
                if v_isShared_2150_ == 0 {
                    v___x_2152_ = v___x_2149_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2153_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2147_);
                    v___x_2152_ = v_reuseFailAlloc_2153_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2152_;
            }
            17 => {
                if v_isShared_2158_ == 0 {
                    v___x_2160_ = v___x_2157_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2161_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
                    v___x_2160_ = v_reuseFailAlloc_2161_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2160_;
            }
            19 => {
                return v___x_2165_;
            }
            20 => {
                if v_isShared_2171_ == 0 {
                    v___x_2173_ = v___x_2170_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2174_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
                    v___x_2173_ = v_reuseFailAlloc_2174_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2173_;
            }
            22 => {
                if crate::leanh::lean_obj_tag(v___y_2177_) == 0 {
                    v_a_2178_ = crate::leanh::lean_ctor_get(v___y_2177_, 0);
                    crate::leanh::lean_inc(v_a_2178_);
                    crate::leanh::lean_dec_ref_known(v___y_2177_, 1);
                    v_a_2080_ = v_a_2178_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___x_2078_);
                    crate::leanh::lean_dec_ref(v_f_2028_);
                    crate::leanh::lean_dec_ref(v_args_2027_);
                    v_a_2179_ = crate::leanh::lean_ctor_get(v___y_2177_, 0);
                    v_isSharedCheck_2186_ = (!crate::leanh::lean_is_exclusive(v___y_2177_)) as u8;
                    if v_isSharedCheck_2186_ == 0 {
                        v___x_2181_ = v___y_2177_;
                        v_isShared_2182_ = v_isSharedCheck_2186_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2179_);
                        crate::leanh::lean_dec(v___y_2177_);
                        v___x_2181_ = crate::leanh::lean_box(0);
                        v_isShared_2182_ = v_isSharedCheck_2186_;
                        state = 23;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_2182_ == 0 {
                    v___x_2184_ = v___x_2181_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2185_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
                    v___x_2184_ = v_reuseFailAlloc_2185_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2184_;
            }
            25 => {
                v___x_2194_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2195_ = lean_array_get_size(v_args_2027_);
                v___x_2196_ = lean_nat_dec_lt(v___x_2194_, v___x_2195_);
                if v___x_2196_ == 0 {
                    v_a_2080_ = v___y_2193_;
                    state = 5;
                    continue;
                } else {
                    v___x_2197_ = lean_nat_dec_le(v___x_2195_, v___x_2195_);
                    if v___x_2197_ == 0 {
                        if v___x_2196_ == 0 {
                            v_a_2080_ = v___y_2193_;
                            state = 5;
                            continue;
                        } else {
                            v___x_2198_ = 0usize;
                            v___x_2199_ = lean_usize_of_nat(v___x_2195_);
                            v___x_2200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg(v_args_2027_, v___x_2198_, v___x_2199_, v___y_2193_, v___y_2033_);
                            v___y_2177_ = v___x_2200_;
                            state = 22;
                            continue;
                        }
                    } else {
                        v___x_2201_ = 0usize;
                        v___x_2202_ = lean_usize_of_nat(v___x_2195_);
                        v___x_2203_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg(v_args_2027_, v___x_2201_, v___x_2202_, v___y_2193_, v___y_2033_);
                        v___y_2177_ = v___x_2203_;
                        state = 22;
                        continue;
                    }
                }
            }
            26 => {
                if v_isShared_2208_ == 0 {
                    v___x_2210_ = v___x_2207_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2211_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
                    v___x_2210_ = v_reuseFailAlloc_2211_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_2210_;
            }
            28 => {
                if v_isShared_2216_ == 0 {
                    v___x_2218_ = v___x_2215_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_2219_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
                    v___x_2218_ = v_reuseFailAlloc_2219_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_2218_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_args_2221_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_f_2222_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_as_2223_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_sz_2224_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_i_2225_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_b_2226_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_2227_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_2228_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_2229_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_2230_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_2231_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_2232_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_2233_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_2234_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_2235_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_2236_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_2237_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_sz_boxed_2238_: usize = 0;
    let mut v_i_boxed_2239_: usize = 0;
    let mut v_res_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2238_ = crate::leanh::lean_unbox_usize(v_sz_2224_);
    crate::leanh::lean_dec(v_sz_2224_);
    v_i_boxed_2239_ = crate::leanh::lean_unbox_usize(v_i_2225_);
    crate::leanh::lean_dec(v_i_2225_);
    v_res_2240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3(v_args_2221_, v_f_2222_, v_as_2223_, v_sz_boxed_2238_, v_i_boxed_2239_, v_b_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
    crate::leanh::lean_dec(v___y_2236_);
    crate::leanh::lean_dec_ref(v___y_2235_);
    crate::leanh::lean_dec(v___y_2234_);
    crate::leanh::lean_dec_ref(v___y_2233_);
    crate::leanh::lean_dec(v___y_2232_);
    crate::leanh::lean_dec_ref(v___y_2231_);
    crate::leanh::lean_dec(v___y_2230_);
    crate::leanh::lean_dec_ref(v___y_2229_);
    crate::leanh::lean_dec(v___y_2228_);
    crate::leanh::lean_dec(v___y_2227_);
    crate::leanh::lean_dec_ref(v_as_2223_);
    return v_res_2240_;
}
pub unsafe fn l_Lean_Meta_Grind_propagateBetaEqs(
    mut v_lams_2241_: *mut crate::leanh::LeanObject,
    mut v_f_2242_: *mut crate::leanh::LeanObject,
    mut v_args_2243_: *mut crate::leanh::LeanObject,
    mut v_a_2244_: *mut crate::leanh::LeanObject,
    mut v_a_2245_: *mut crate::leanh::LeanObject,
    mut v_a_2246_: *mut crate::leanh::LeanObject,
    mut v_a_2247_: *mut crate::leanh::LeanObject,
    mut v_a_2248_: *mut crate::leanh::LeanObject,
    mut v_a_2249_: *mut crate::leanh::LeanObject,
    mut v_a_2250_: *mut crate::leanh::LeanObject,
    mut v_a_2251_: *mut crate::leanh::LeanObject,
    mut v_a_2252_: *mut crate::leanh::LeanObject,
    mut v_a_2253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: u8 = 0;
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2260_: usize = 0;
    let mut v___x_2261_: usize = 0;
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2266_: u8 = 0;
    let mut v_fst_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2275_: u8 = 0;
    let mut v_a_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2279_: u8 = 0;
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2283_: u8 = 0;
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2255_ = lean_array_get_size(v_args_2243_);
                v___x_2256_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2257_ = lean_nat_dec_eq(v___x_2255_, v___x_2256_);
                if v___x_2257_ == 0 {
                    v___x_2258_ = crate::leanh::lean_box(0);
                    v___x_2259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__0;
                    v_sz_2260_ = lean_array_size(v_lams_2241_);
                    v___x_2261_ = 0usize;
                    v___x_2262_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3(v_args_2243_, v_f_2242_, v_lams_2241_, v_sz_2260_, v___x_2261_, v___x_2259_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_);
                    if crate::leanh::lean_obj_tag(v___x_2262_) == 0 {
                        v_a_2263_ = crate::leanh::lean_ctor_get(v___x_2262_, 0);
                        v_isSharedCheck_2275_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2262_)) as u8;
                        if v_isSharedCheck_2275_ == 0 {
                            v___x_2265_ = v___x_2262_;
                            v_isShared_2266_ = v_isSharedCheck_2275_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2263_);
                            crate::leanh::lean_dec(v___x_2262_);
                            v___x_2265_ = crate::leanh::lean_box(0);
                            v_isShared_2266_ = v_isSharedCheck_2275_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2276_ = crate::leanh::lean_ctor_get(v___x_2262_, 0);
                        v_isSharedCheck_2283_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2262_)) as u8;
                        if v_isSharedCheck_2283_ == 0 {
                            v___x_2278_ = v___x_2262_;
                            v_isShared_2279_ = v_isSharedCheck_2283_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2276_);
                            crate::leanh::lean_dec(v___x_2262_);
                            v___x_2278_ = crate::leanh::lean_box(0);
                            v_isShared_2279_ = v_isSharedCheck_2283_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_args_2243_);
                    crate::leanh::lean_dec_ref(v_f_2242_);
                    v___x_2284_ = crate::leanh::lean_box(0);
                    v___x_2285_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2285_, 0, v___x_2284_);
                    return v___x_2285_;
                }
            }
            1 => {
                v_fst_2267_ = crate::leanh::lean_ctor_get(v_a_2263_, 0);
                crate::leanh::lean_inc(v_fst_2267_);
                crate::leanh::lean_dec(v_a_2263_);
                if crate::leanh::lean_obj_tag(v_fst_2267_) == 0 {
                    if v_isShared_2266_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2265_, 0, v___x_2258_);
                        v___x_2269_ = v___x_2265_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2270_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2258_);
                        v___x_2269_ = v_reuseFailAlloc_2270_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_2271_ = crate::leanh::lean_ctor_get(v_fst_2267_, 0);
                    crate::leanh::lean_inc(v_val_2271_);
                    crate::leanh::lean_dec_ref_known(v_fst_2267_, 1);
                    if v_isShared_2266_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2265_, 0, v_val_2271_);
                        v___x_2273_ = v___x_2265_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2274_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_val_2271_);
                        v___x_2273_ = v_reuseFailAlloc_2274_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2269_;
            }
            3 => {
                return v___x_2273_;
            }
            4 => {
                if v_isShared_2279_ == 0 {
                    v___x_2281_ = v___x_2278_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2282_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
                    v___x_2281_ = v_reuseFailAlloc_2282_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2281_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_propagateBetaEqs___boxed(
    mut v_lams_2286_: *mut crate::leanh::LeanObject,
    mut v_f_2287_: *mut crate::leanh::LeanObject,
    mut v_args_2288_: *mut crate::leanh::LeanObject,
    mut v_a_2289_: *mut crate::leanh::LeanObject,
    mut v_a_2290_: *mut crate::leanh::LeanObject,
    mut v_a_2291_: *mut crate::leanh::LeanObject,
    mut v_a_2292_: *mut crate::leanh::LeanObject,
    mut v_a_2293_: *mut crate::leanh::LeanObject,
    mut v_a_2294_: *mut crate::leanh::LeanObject,
    mut v_a_2295_: *mut crate::leanh::LeanObject,
    mut v_a_2296_: *mut crate::leanh::LeanObject,
    mut v_a_2297_: *mut crate::leanh::LeanObject,
    mut v_a_2298_: *mut crate::leanh::LeanObject,
    mut v_a_2299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2300_ = l_Lean_Meta_Grind_propagateBetaEqs(
        v_lams_2286_,
        v_f_2287_,
        v_args_2288_,
        v_a_2289_,
        v_a_2290_,
        v_a_2291_,
        v_a_2292_,
        v_a_2293_,
        v_a_2294_,
        v_a_2295_,
        v_a_2296_,
        v_a_2297_,
        v_a_2298_,
    );
    crate::leanh::lean_dec(v_a_2298_);
    crate::leanh::lean_dec_ref(v_a_2297_);
    crate::leanh::lean_dec(v_a_2296_);
    crate::leanh::lean_dec_ref(v_a_2295_);
    crate::leanh::lean_dec(v_a_2294_);
    crate::leanh::lean_dec_ref(v_a_2293_);
    crate::leanh::lean_dec(v_a_2292_);
    crate::leanh::lean_dec_ref(v_a_2291_);
    crate::leanh::lean_dec(v_a_2290_);
    crate::leanh::lean_dec(v_a_2289_);
    crate::leanh::lean_dec_ref(v_lams_2286_);
    return v_res_2300_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0(
    mut v_as_2301_: *mut crate::leanh::LeanObject,
    mut v_sz_2302_: usize,
    mut v_i_2303_: usize,
    mut v_b_2304_: *mut crate::leanh::LeanObject,
    mut v___y_2305_: *mut crate::leanh::LeanObject,
    mut v___y_2306_: *mut crate::leanh::LeanObject,
    mut v___y_2307_: *mut crate::leanh::LeanObject,
    mut v___y_2308_: *mut crate::leanh::LeanObject,
    mut v___y_2309_: *mut crate::leanh::LeanObject,
    mut v___y_2310_: *mut crate::leanh::LeanObject,
    mut v___y_2311_: *mut crate::leanh::LeanObject,
    mut v___y_2312_: *mut crate::leanh::LeanObject,
    mut v___y_2313_: *mut crate::leanh::LeanObject,
    mut v___y_2314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2316_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(v_as_2301_, v_sz_2302_, v_i_2303_, v_b_2304_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
    return v___x_2316_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___boxed(
    mut v_as_2317_: *mut crate::leanh::LeanObject,
    mut v_sz_2318_: *mut crate::leanh::LeanObject,
    mut v_i_2319_: *mut crate::leanh::LeanObject,
    mut v_b_2320_: *mut crate::leanh::LeanObject,
    mut v___y_2321_: *mut crate::leanh::LeanObject,
    mut v___y_2322_: *mut crate::leanh::LeanObject,
    mut v___y_2323_: *mut crate::leanh::LeanObject,
    mut v___y_2324_: *mut crate::leanh::LeanObject,
    mut v___y_2325_: *mut crate::leanh::LeanObject,
    mut v___y_2326_: *mut crate::leanh::LeanObject,
    mut v___y_2327_: *mut crate::leanh::LeanObject,
    mut v___y_2328_: *mut crate::leanh::LeanObject,
    mut v___y_2329_: *mut crate::leanh::LeanObject,
    mut v___y_2330_: *mut crate::leanh::LeanObject,
    mut v___y_2331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2332_: usize = 0;
    let mut v_i_boxed_2333_: usize = 0;
    let mut v_res_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2332_ = crate::leanh::lean_unbox_usize(v_sz_2318_);
    crate::leanh::lean_dec(v_sz_2318_);
    v_i_boxed_2333_ = crate::leanh::lean_unbox_usize(v_i_2319_);
    crate::leanh::lean_dec(v_i_2319_);
    v_res_2334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0(v_as_2317_, v_sz_boxed_2332_, v_i_boxed_2333_, v_b_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
    crate::leanh::lean_dec(v___y_2330_);
    crate::leanh::lean_dec_ref(v___y_2329_);
    crate::leanh::lean_dec(v___y_2328_);
    crate::leanh::lean_dec_ref(v___y_2327_);
    crate::leanh::lean_dec(v___y_2326_);
    crate::leanh::lean_dec_ref(v___y_2325_);
    crate::leanh::lean_dec(v___y_2324_);
    crate::leanh::lean_dec_ref(v___y_2323_);
    crate::leanh::lean_dec(v___y_2322_);
    crate::leanh::lean_dec(v___y_2321_);
    crate::leanh::lean_dec_ref(v_as_2317_);
    return v_res_2334_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1(
    mut v_cls_2335_: *mut crate::leanh::LeanObject,
    mut v_msg_2336_: *mut crate::leanh::LeanObject,
    mut v___y_2337_: *mut crate::leanh::LeanObject,
    mut v___y_2338_: *mut crate::leanh::LeanObject,
    mut v___y_2339_: *mut crate::leanh::LeanObject,
    mut v___y_2340_: *mut crate::leanh::LeanObject,
    mut v___y_2341_: *mut crate::leanh::LeanObject,
    mut v___y_2342_: *mut crate::leanh::LeanObject,
    mut v___y_2343_: *mut crate::leanh::LeanObject,
    mut v___y_2344_: *mut crate::leanh::LeanObject,
    mut v___y_2345_: *mut crate::leanh::LeanObject,
    mut v___y_2346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2348_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg(
        v_cls_2335_,
        v_msg_2336_,
        v___y_2343_,
        v___y_2344_,
        v___y_2345_,
        v___y_2346_,
    );
    return v___x_2348_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___boxed(
    mut v_cls_2349_: *mut crate::leanh::LeanObject,
    mut v_msg_2350_: *mut crate::leanh::LeanObject,
    mut v___y_2351_: *mut crate::leanh::LeanObject,
    mut v___y_2352_: *mut crate::leanh::LeanObject,
    mut v___y_2353_: *mut crate::leanh::LeanObject,
    mut v___y_2354_: *mut crate::leanh::LeanObject,
    mut v___y_2355_: *mut crate::leanh::LeanObject,
    mut v___y_2356_: *mut crate::leanh::LeanObject,
    mut v___y_2357_: *mut crate::leanh::LeanObject,
    mut v___y_2358_: *mut crate::leanh::LeanObject,
    mut v___y_2359_: *mut crate::leanh::LeanObject,
    mut v___y_2360_: *mut crate::leanh::LeanObject,
    mut v___y_2361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2362_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1(
        v_cls_2349_,
        v_msg_2350_,
        v___y_2351_,
        v___y_2352_,
        v___y_2353_,
        v___y_2354_,
        v___y_2355_,
        v___y_2356_,
        v___y_2357_,
        v___y_2358_,
        v___y_2359_,
        v___y_2360_,
    );
    crate::leanh::lean_dec(v___y_2360_);
    crate::leanh::lean_dec_ref(v___y_2359_);
    crate::leanh::lean_dec(v___y_2358_);
    crate::leanh::lean_dec_ref(v___y_2357_);
    crate::leanh::lean_dec(v___y_2356_);
    crate::leanh::lean_dec_ref(v___y_2355_);
    crate::leanh::lean_dec(v___y_2354_);
    crate::leanh::lean_dec_ref(v___y_2353_);
    crate::leanh::lean_dec(v___y_2352_);
    crate::leanh::lean_dec(v___y_2351_);
    return v_res_2362_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2(
    mut v_as_2363_: *mut crate::leanh::LeanObject,
    mut v_i_2364_: usize,
    mut v_stop_2365_: usize,
    mut v_b_2366_: *mut crate::leanh::LeanObject,
    mut v___y_2367_: *mut crate::leanh::LeanObject,
    mut v___y_2368_: *mut crate::leanh::LeanObject,
    mut v___y_2369_: *mut crate::leanh::LeanObject,
    mut v___y_2370_: *mut crate::leanh::LeanObject,
    mut v___y_2371_: *mut crate::leanh::LeanObject,
    mut v___y_2372_: *mut crate::leanh::LeanObject,
    mut v___y_2373_: *mut crate::leanh::LeanObject,
    mut v___y_2374_: *mut crate::leanh::LeanObject,
    mut v___y_2375_: *mut crate::leanh::LeanObject,
    mut v___y_2376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg(v_as_2363_, v_i_2364_, v_stop_2365_, v_b_2366_, v___y_2367_);
    return v___x_2378_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___boxed(
    mut v_as_2379_: *mut crate::leanh::LeanObject,
    mut v_i_2380_: *mut crate::leanh::LeanObject,
    mut v_stop_2381_: *mut crate::leanh::LeanObject,
    mut v_b_2382_: *mut crate::leanh::LeanObject,
    mut v___y_2383_: *mut crate::leanh::LeanObject,
    mut v___y_2384_: *mut crate::leanh::LeanObject,
    mut v___y_2385_: *mut crate::leanh::LeanObject,
    mut v___y_2386_: *mut crate::leanh::LeanObject,
    mut v___y_2387_: *mut crate::leanh::LeanObject,
    mut v___y_2388_: *mut crate::leanh::LeanObject,
    mut v___y_2389_: *mut crate::leanh::LeanObject,
    mut v___y_2390_: *mut crate::leanh::LeanObject,
    mut v___y_2391_: *mut crate::leanh::LeanObject,
    mut v___y_2392_: *mut crate::leanh::LeanObject,
    mut v___y_2393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2394_: usize = 0;
    let mut v_stop_boxed_2395_: usize = 0;
    let mut v_res_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2394_ = crate::leanh::lean_unbox_usize(v_i_2380_);
    crate::leanh::lean_dec(v_i_2380_);
    v_stop_boxed_2395_ = crate::leanh::lean_unbox_usize(v_stop_2381_);
    crate::leanh::lean_dec(v_stop_2381_);
    v_res_2396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2(v_as_2379_, v_i_boxed_2394_, v_stop_boxed_2395_, v_b_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
    crate::leanh::lean_dec(v___y_2392_);
    crate::leanh::lean_dec_ref(v___y_2391_);
    crate::leanh::lean_dec(v___y_2390_);
    crate::leanh::lean_dec_ref(v___y_2389_);
    crate::leanh::lean_dec(v___y_2388_);
    crate::leanh::lean_dec_ref(v___y_2387_);
    crate::leanh::lean_dec(v___y_2386_);
    crate::leanh::lean_dec_ref(v___y_2385_);
    crate::leanh::lean_dec(v___y_2384_);
    crate::leanh::lean_dec(v___y_2383_);
    crate::leanh::lean_dec_ref(v_as_2379_);
    return v_res_2396_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go(
    mut v_f_2397_: *mut crate::leanh::LeanObject,
    mut v_a_2398_: *mut crate::leanh::LeanObject,
    mut v_a_2399_: *mut crate::leanh::LeanObject,
    mut v_a_2400_: *mut crate::leanh::LeanObject,
    mut v_a_2401_: *mut crate::leanh::LeanObject,
    mut v_a_2402_: *mut crate::leanh::LeanObject,
    mut v_a_2403_: *mut crate::leanh::LeanObject,
    mut v_a_2404_: *mut crate::leanh::LeanObject,
    mut v_a_2405_: *mut crate::leanh::LeanObject,
    mut v_a_2406_: *mut crate::leanh::LeanObject,
    mut v_a_2407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2413_: u8 = 0;
    let mut v___y_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: u8 = 0;
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2435_: u8 = 0;
    let mut v_hasLambdas_2436_: u8 = 0;
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2441_: u8 = 0;
    let mut v_isSharedCheck_2442_: u8 = 0;
    let mut v_a_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2446_: u8 = 0;
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2450_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2409_ = l_Lean_Meta_Grind_getRootENode_x3f___redArg(v_f_2397_, v_a_2398_);
                if crate::leanh::lean_obj_tag(v___x_2409_) == 0 {
                    v_a_2410_ = crate::leanh::lean_ctor_get(v___x_2409_, 0);
                    v_isSharedCheck_2442_ = (!crate::leanh::lean_is_exclusive(v___x_2409_)) as u8;
                    if v_isSharedCheck_2442_ == 0 {
                        v___x_2412_ = v___x_2409_;
                        v_isShared_2413_ = v_isSharedCheck_2442_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2410_);
                        crate::leanh::lean_dec(v___x_2409_);
                        v___x_2412_ = crate::leanh::lean_box(0);
                        v_isShared_2413_ = v_isSharedCheck_2442_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2443_ = crate::leanh::lean_ctor_get(v___x_2409_, 0);
                    v_isSharedCheck_2450_ = (!crate::leanh::lean_is_exclusive(v___x_2409_)) as u8;
                    if v_isSharedCheck_2450_ == 0 {
                        v___x_2445_ = v___x_2409_;
                        v_isShared_2446_ = v_isSharedCheck_2450_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2443_);
                        crate::leanh::lean_dec(v___x_2409_);
                        v___x_2445_ = crate::leanh::lean_box(0);
                        v_isShared_2446_ = v_isSharedCheck_2450_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2410_) == 1 {
                    v_val_2432_ = crate::leanh::lean_ctor_get(v_a_2410_, 0);
                    v_isSharedCheck_2441_ = (!crate::leanh::lean_is_exclusive(v_a_2410_)) as u8;
                    if v_isSharedCheck_2441_ == 0 {
                        v___x_2434_ = v_a_2410_;
                        v_isShared_2435_ = v_isSharedCheck_2441_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2432_);
                        crate::leanh::lean_dec(v_a_2410_);
                        v___x_2434_ = crate::leanh::lean_box(0);
                        v_isShared_2435_ = v_isSharedCheck_2441_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2410_);
                    v___y_2415_ = v_a_2398_;
                    v___y_2416_ = v_a_2399_;
                    v___y_2417_ = v_a_2400_;
                    v___y_2418_ = v_a_2401_;
                    v___y_2419_ = v_a_2402_;
                    v___y_2420_ = v_a_2403_;
                    v___y_2421_ = v_a_2404_;
                    v___y_2422_ = v_a_2405_;
                    v___y_2423_ = v_a_2406_;
                    v___y_2424_ = v_a_2407_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_f_2397_) == 5 {
                    crate::leanh::lean_del_object(v___x_2412_);
                    v_fn_2425_ = crate::leanh::lean_ctor_get(v_f_2397_, 0);
                    v_f_2397_ = v_fn_2425_;
                    v_a_2398_ = v___y_2415_;
                    v_a_2399_ = v___y_2416_;
                    v_a_2400_ = v___y_2417_;
                    v_a_2401_ = v___y_2418_;
                    v_a_2402_ = v___y_2419_;
                    v_a_2403_ = v___y_2420_;
                    v_a_2404_ = v___y_2421_;
                    v_a_2405_ = v___y_2422_;
                    v_a_2406_ = v___y_2423_;
                    v_a_2407_ = v___y_2424_;
                    state = 0;
                    continue;
                } else {
                    v___x_2427_ = 0;
                    v___x_2428_ = crate::leanh::lean_box((v___x_2427_) as usize);
                    if v_isShared_2413_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2412_, 0, v___x_2428_);
                        v___x_2430_ = v___x_2412_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2431_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2428_);
                        v___x_2430_ = v_reuseFailAlloc_2431_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_2430_;
            }
            4 => {
                v_hasLambdas_2436_ = crate::leanh::lean_ctor_get_uint8(
                    v_val_2432_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 12 + 3) as u32,
                );
                crate::leanh::lean_dec(v_val_2432_);
                if v_hasLambdas_2436_ == 0 {
                    crate::leanh::lean_del_object(v___x_2434_);
                    v___y_2415_ = v_a_2398_;
                    v___y_2416_ = v_a_2399_;
                    v___y_2417_ = v_a_2400_;
                    v___y_2418_ = v_a_2401_;
                    v___y_2419_ = v_a_2402_;
                    v___y_2420_ = v_a_2403_;
                    v___y_2421_ = v_a_2404_;
                    v___y_2422_ = v_a_2405_;
                    v___y_2423_ = v_a_2406_;
                    v___y_2424_ = v_a_2407_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_del_object(v___x_2412_);
                    v___x_2437_ = crate::leanh::lean_box((v_hasLambdas_2436_) as usize);
                    if v_isShared_2435_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2434_, 0);
                        crate::leanh::lean_ctor_set(v___x_2434_, 0, v___x_2437_);
                        v___x_2439_ = v___x_2434_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2440_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2437_);
                        v___x_2439_ = v_reuseFailAlloc_2440_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_2439_;
            }
            6 => {
                if v_isShared_2446_ == 0 {
                    v___x_2448_ = v___x_2445_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2449_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
                    v___x_2448_ = v_reuseFailAlloc_2449_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2448_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go___boxed(
    mut v_f_2451_: *mut crate::leanh::LeanObject,
    mut v_a_2452_: *mut crate::leanh::LeanObject,
    mut v_a_2453_: *mut crate::leanh::LeanObject,
    mut v_a_2454_: *mut crate::leanh::LeanObject,
    mut v_a_2455_: *mut crate::leanh::LeanObject,
    mut v_a_2456_: *mut crate::leanh::LeanObject,
    mut v_a_2457_: *mut crate::leanh::LeanObject,
    mut v_a_2458_: *mut crate::leanh::LeanObject,
    mut v_a_2459_: *mut crate::leanh::LeanObject,
    mut v_a_2460_: *mut crate::leanh::LeanObject,
    mut v_a_2461_: *mut crate::leanh::LeanObject,
    mut v_a_2462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2463_ =
        l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go(
            v_f_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_,
            v_a_2459_, v_a_2460_, v_a_2461_,
        );
    crate::leanh::lean_dec(v_a_2461_);
    crate::leanh::lean_dec_ref(v_a_2460_);
    crate::leanh::lean_dec(v_a_2459_);
    crate::leanh::lean_dec_ref(v_a_2458_);
    crate::leanh::lean_dec(v_a_2457_);
    crate::leanh::lean_dec_ref(v_a_2456_);
    crate::leanh::lean_dec(v_a_2455_);
    crate::leanh::lean_dec_ref(v_a_2454_);
    crate::leanh::lean_dec(v_a_2453_);
    crate::leanh::lean_dec(v_a_2452_);
    crate::leanh::lean_dec_ref(v_f_2451_);
    return v_res_2463_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget(
    mut v_e_2464_: *mut crate::leanh::LeanObject,
    mut v_a_2465_: *mut crate::leanh::LeanObject,
    mut v_a_2466_: *mut crate::leanh::LeanObject,
    mut v_a_2467_: *mut crate::leanh::LeanObject,
    mut v_a_2468_: *mut crate::leanh::LeanObject,
    mut v_a_2469_: *mut crate::leanh::LeanObject,
    mut v_a_2470_: *mut crate::leanh::LeanObject,
    mut v_a_2471_: *mut crate::leanh::LeanObject,
    mut v_a_2472_: *mut crate::leanh::LeanObject,
    mut v_a_2473_: *mut crate::leanh::LeanObject,
    mut v_a_2474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_2464_) == 5 {
        let mut v_fn_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_fn_2476_ = crate::leanh::lean_ctor_get(v_e_2464_, 0);
        v___x_2477_ =
            l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go(
                v_fn_2476_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_,
                v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_,
            );
        return v___x_2477_;
    } else {
        let mut v___x_2478_: u8 = 0;
        let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2478_ = 0;
        v___x_2479_ = crate::leanh::lean_box((v___x_2478_) as usize);
        v___x_2480_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2480_, 0, v___x_2479_);
        return v___x_2480_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget___boxed(
    mut v_e_2481_: *mut crate::leanh::LeanObject,
    mut v_a_2482_: *mut crate::leanh::LeanObject,
    mut v_a_2483_: *mut crate::leanh::LeanObject,
    mut v_a_2484_: *mut crate::leanh::LeanObject,
    mut v_a_2485_: *mut crate::leanh::LeanObject,
    mut v_a_2486_: *mut crate::leanh::LeanObject,
    mut v_a_2487_: *mut crate::leanh::LeanObject,
    mut v_a_2488_: *mut crate::leanh::LeanObject,
    mut v_a_2489_: *mut crate::leanh::LeanObject,
    mut v_a_2490_: *mut crate::leanh::LeanObject,
    mut v_a_2491_: *mut crate::leanh::LeanObject,
    mut v_a_2492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2493_ = l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget(
        v_e_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_,
        v_a_2489_, v_a_2490_, v_a_2491_,
    );
    crate::leanh::lean_dec(v_a_2491_);
    crate::leanh::lean_dec_ref(v_a_2490_);
    crate::leanh::lean_dec(v_a_2489_);
    crate::leanh::lean_dec_ref(v_a_2488_);
    crate::leanh::lean_dec(v_a_2487_);
    crate::leanh::lean_dec_ref(v_a_2486_);
    crate::leanh::lean_dec(v_a_2485_);
    crate::leanh::lean_dec_ref(v_a_2484_);
    crate::leanh::lean_dec(v_a_2483_);
    crate::leanh::lean_dec(v_a_2482_);
    crate::leanh::lean_dec_ref(v_e_2481_);
    return v_res_2493_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___lam__0(
    mut v_fst_2494_: *mut crate::leanh::LeanObject,
    mut v_snd_2495_: *mut crate::leanh::LeanObject,
    mut v___x_2496_: *mut crate::leanh::LeanObject,
    mut v_____r_2497_: *mut crate::leanh::LeanObject,
    mut v___y_2498_: *mut crate::leanh::LeanObject,
    mut v___y_2499_: *mut crate::leanh::LeanObject,
    mut v___y_2500_: *mut crate::leanh::LeanObject,
    mut v___y_2501_: *mut crate::leanh::LeanObject,
    mut v___y_2502_: *mut crate::leanh::LeanObject,
    mut v___y_2503_: *mut crate::leanh::LeanObject,
    mut v___y_2504_: *mut crate::leanh::LeanObject,
    mut v___y_2505_: *mut crate::leanh::LeanObject,
    mut v___y_2506_: *mut crate::leanh::LeanObject,
    mut v___y_2507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_fst_2494_) == 5 {
        let mut v_fn_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_arg_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_fn_2509_ = crate::leanh::lean_ctor_get(v_fst_2494_, 0);
        crate::leanh::lean_inc_ref(v_fn_2509_);
        v_arg_2510_ = crate::leanh::lean_ctor_get(v_fst_2494_, 1);
        crate::leanh::lean_inc_ref(v_arg_2510_);
        crate::leanh::lean_dec_ref_known(v_fst_2494_, 2);
        v___x_2511_ = lean_array_push(v_snd_2495_, v_arg_2510_);
        v___x_2512_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2512_, 0, v_fn_2509_);
        crate::leanh::lean_ctor_set(v___x_2512_, 1, v___x_2511_);
        v___x_2513_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2513_, 0, v___x_2496_);
        crate::leanh::lean_ctor_set(v___x_2513_, 1, v___x_2512_);
        v___x_2514_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2514_, 0, v___x_2513_);
        v___x_2515_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2515_, 0, v___x_2514_);
        return v___x_2515_;
    } else {
        let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_2496_);
        v___x_2516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__9;
        v___x_2517_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2517_, 0, v_fst_2494_);
        crate::leanh::lean_ctor_set(v___x_2517_, 1, v_snd_2495_);
        v___x_2518_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2518_, 0, v___x_2516_);
        crate::leanh::lean_ctor_set(v___x_2518_, 1, v___x_2517_);
        v___x_2519_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2519_, 0, v___x_2518_);
        v___x_2520_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2520_, 0, v___x_2519_);
        return v___x_2520_;
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___lam__0___boxed(
    mut v_fst_2521_: *mut crate::leanh::LeanObject,
    mut v_snd_2522_: *mut crate::leanh::LeanObject,
    mut v___x_2523_: *mut crate::leanh::LeanObject,
    mut v_____r_2524_: *mut crate::leanh::LeanObject,
    mut v___y_2525_: *mut crate::leanh::LeanObject,
    mut v___y_2526_: *mut crate::leanh::LeanObject,
    mut v___y_2527_: *mut crate::leanh::LeanObject,
    mut v___y_2528_: *mut crate::leanh::LeanObject,
    mut v___y_2529_: *mut crate::leanh::LeanObject,
    mut v___y_2530_: *mut crate::leanh::LeanObject,
    mut v___y_2531_: *mut crate::leanh::LeanObject,
    mut v___y_2532_: *mut crate::leanh::LeanObject,
    mut v___y_2533_: *mut crate::leanh::LeanObject,
    mut v___y_2534_: *mut crate::leanh::LeanObject,
    mut v___y_2535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2536_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___lam__0(v_fst_2521_, v_snd_2522_, v___x_2523_, v_____r_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
    crate::leanh::lean_dec(v___y_2534_);
    crate::leanh::lean_dec_ref(v___y_2533_);
    crate::leanh::lean_dec(v___y_2532_);
    crate::leanh::lean_dec_ref(v___y_2531_);
    crate::leanh::lean_dec(v___y_2530_);
    crate::leanh::lean_dec_ref(v___y_2529_);
    crate::leanh::lean_dec(v___y_2528_);
    crate::leanh::lean_dec_ref(v___y_2527_);
    crate::leanh::lean_dec(v___y_2526_);
    crate::leanh::lean_dec(v___y_2525_);
    return v_res_2536_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg(
    mut v_a_2537_: *mut crate::leanh::LeanObject,
    mut v___y_2538_: *mut crate::leanh::LeanObject,
    mut v___y_2539_: *mut crate::leanh::LeanObject,
    mut v___y_2540_: *mut crate::leanh::LeanObject,
    mut v___y_2541_: *mut crate::leanh::LeanObject,
    mut v___y_2542_: *mut crate::leanh::LeanObject,
    mut v___y_2543_: *mut crate::leanh::LeanObject,
    mut v___y_2544_: *mut crate::leanh::LeanObject,
    mut v___y_2545_: *mut crate::leanh::LeanObject,
    mut v___y_2546_: *mut crate::leanh::LeanObject,
    mut v___y_2547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2554_: u8 = 0;
    let mut v_a_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2561_: u8 = 0;
    let mut v_a_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2565_: u8 = 0;
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2569_: u8 = 0;
    let mut v_snd_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: u8 = 0;
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasLambdas_2580_: u8 = 0;
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2592_: u8 = 0;
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2596_: u8 = 0;
    let mut v_a_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2600_: u8 = 0;
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2604_: u8 = 0;
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2610_: u8 = 0;
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2614_: u8 = 0;
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_2570_ = crate::leanh::lean_ctor_get(v_a_2537_, 1);
                crate::leanh::lean_inc(v_snd_2570_);
                crate::leanh::lean_dec_ref(v_a_2537_);
                v_fst_2571_ = crate::leanh::lean_ctor_get(v_snd_2570_, 0);
                crate::leanh::lean_inc(v_fst_2571_);
                v_snd_2572_ = crate::leanh::lean_ctor_get(v_snd_2570_, 1);
                crate::leanh::lean_inc(v_snd_2572_);
                crate::leanh::lean_dec(v_snd_2570_);
                v___x_2573_ = crate::leanh::lean_box(0);
                v___x_2574_ = lean_array_get_size(v_snd_2572_);
                v___x_2575_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2576_ = lean_nat_dec_eq(v___x_2574_, v___x_2575_);
                if v___x_2576_ == 0 {
                    v___x_2577_ =
                        l_Lean_Meta_Grind_getRootENode_x3f___redArg(v_fst_2571_, v___y_2538_);
                    if crate::leanh::lean_obj_tag(v___x_2577_) == 0 {
                        v_a_2578_ = crate::leanh::lean_ctor_get(v___x_2577_, 0);
                        crate::leanh::lean_inc(v_a_2578_);
                        crate::leanh::lean_dec_ref_known(v___x_2577_, 1);
                        if crate::leanh::lean_obj_tag(v_a_2578_) == 1 {
                            v_val_2579_ = crate::leanh::lean_ctor_get(v_a_2578_, 0);
                            crate::leanh::lean_inc(v_val_2579_);
                            crate::leanh::lean_dec_ref_known(v_a_2578_, 1);
                            v_hasLambdas_2580_ = crate::leanh::lean_ctor_get_uint8(
                                v_val_2579_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 12 + 3)
                                    as u32,
                            );
                            if v_hasLambdas_2580_ == 0 {
                                crate::leanh::lean_dec(v_val_2579_);
                                v___x_2581_ = crate::leanh::lean_box(0);
                                v___x_2582_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___lam__0(v_fst_2571_, v_snd_2572_, v___x_2573_, v___x_2581_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
                                v___y_2550_ = v___x_2582_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2583_ = l_Lean_Meta_Grind_getEqcLambdas(
                                    v_val_2579_,
                                    v___y_2538_,
                                    v___y_2539_,
                                    v___y_2540_,
                                    v___y_2541_,
                                    v___y_2542_,
                                    v___y_2543_,
                                    v___y_2544_,
                                    v___y_2545_,
                                    v___y_2546_,
                                    v___y_2547_,
                                );
                                crate::leanh::lean_dec(v_val_2579_);
                                if crate::leanh::lean_obj_tag(v___x_2583_) == 0 {
                                    v_a_2584_ = crate::leanh::lean_ctor_get(v___x_2583_, 0);
                                    crate::leanh::lean_inc(v_a_2584_);
                                    crate::leanh::lean_dec_ref_known(v___x_2583_, 1);
                                    crate::leanh::lean_inc(v_snd_2572_);
                                    v___x_2585_ = l_Array_reverse___redArg(v_snd_2572_);
                                    crate::leanh::lean_inc(v_fst_2571_);
                                    v___x_2586_ = l_Lean_Meta_Grind_propagateBetaEqs(
                                        v_a_2584_,
                                        v_fst_2571_,
                                        v___x_2585_,
                                        v___y_2538_,
                                        v___y_2539_,
                                        v___y_2540_,
                                        v___y_2541_,
                                        v___y_2542_,
                                        v___y_2543_,
                                        v___y_2544_,
                                        v___y_2545_,
                                        v___y_2546_,
                                        v___y_2547_,
                                    );
                                    crate::leanh::lean_dec(v_a_2584_);
                                    if crate::leanh::lean_obj_tag(v___x_2586_) == 0 {
                                        v_a_2587_ = crate::leanh::lean_ctor_get(v___x_2586_, 0);
                                        crate::leanh::lean_inc(v_a_2587_);
                                        crate::leanh::lean_dec_ref_known(v___x_2586_, 1);
                                        v___x_2588_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___lam__0(v_fst_2571_, v_snd_2572_, v___x_2573_, v_a_2587_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
                                        v___y_2550_ = v___x_2588_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_snd_2572_);
                                        crate::leanh::lean_dec(v_fst_2571_);
                                        v_a_2589_ = crate::leanh::lean_ctor_get(v___x_2586_, 0);
                                        v_isSharedCheck_2596_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2586_)) as u8;
                                        if v_isSharedCheck_2596_ == 0 {
                                            v___x_2591_ = v___x_2586_;
                                            v_isShared_2592_ = v_isSharedCheck_2596_;
                                            state = 6;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2589_);
                                            crate::leanh::lean_dec(v___x_2586_);
                                            v___x_2591_ = crate::leanh::lean_box(0);
                                            v_isShared_2592_ = v_isSharedCheck_2596_;
                                            state = 6;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_snd_2572_);
                                    crate::leanh::lean_dec(v_fst_2571_);
                                    v_a_2597_ = crate::leanh::lean_ctor_get(v___x_2583_, 0);
                                    v_isSharedCheck_2604_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2583_)) as u8;
                                    if v_isSharedCheck_2604_ == 0 {
                                        v___x_2599_ = v___x_2583_;
                                        v_isShared_2600_ = v_isSharedCheck_2604_;
                                        state = 8;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2597_);
                                        crate::leanh::lean_dec(v___x_2583_);
                                        v___x_2599_ = crate::leanh::lean_box(0);
                                        v_isShared_2600_ = v_isSharedCheck_2604_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2578_);
                            v___x_2605_ = crate::leanh::lean_box(0);
                            v___x_2606_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___lam__0(v_fst_2571_, v_snd_2572_, v___x_2573_, v___x_2605_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
                            v___y_2550_ = v___x_2606_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_snd_2572_);
                        crate::leanh::lean_dec(v_fst_2571_);
                        v_a_2607_ = crate::leanh::lean_ctor_get(v___x_2577_, 0);
                        v_isSharedCheck_2614_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2577_)) as u8;
                        if v_isSharedCheck_2614_ == 0 {
                            v___x_2609_ = v___x_2577_;
                            v_isShared_2610_ = v_isSharedCheck_2614_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2607_);
                            crate::leanh::lean_dec(v___x_2577_);
                            v___x_2609_ = crate::leanh::lean_box(0);
                            v_isShared_2610_ = v_isSharedCheck_2614_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    v___x_2615_ = crate::leanh::lean_box(0);
                    v___x_2616_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___lam__0(v_fst_2571_, v_snd_2572_, v___x_2573_, v___x_2615_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
                    v___y_2550_ = v___x_2616_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_2550_) == 0 {
                    v_a_2551_ = crate::leanh::lean_ctor_get(v___y_2550_, 0);
                    v_isSharedCheck_2561_ = (!crate::leanh::lean_is_exclusive(v___y_2550_)) as u8;
                    if v_isSharedCheck_2561_ == 0 {
                        v___x_2553_ = v___y_2550_;
                        v_isShared_2554_ = v_isSharedCheck_2561_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2551_);
                        crate::leanh::lean_dec(v___y_2550_);
                        v___x_2553_ = crate::leanh::lean_box(0);
                        v_isShared_2554_ = v_isSharedCheck_2561_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2562_ = crate::leanh::lean_ctor_get(v___y_2550_, 0);
                    v_isSharedCheck_2569_ = (!crate::leanh::lean_is_exclusive(v___y_2550_)) as u8;
                    if v_isSharedCheck_2569_ == 0 {
                        v___x_2564_ = v___y_2550_;
                        v_isShared_2565_ = v_isSharedCheck_2569_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2562_);
                        crate::leanh::lean_dec(v___y_2550_);
                        v___x_2564_ = crate::leanh::lean_box(0);
                        v_isShared_2565_ = v_isSharedCheck_2569_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_2551_) == 0 {
                    v_a_2555_ = crate::leanh::lean_ctor_get(v_a_2551_, 0);
                    crate::leanh::lean_inc(v_a_2555_);
                    crate::leanh::lean_dec_ref_known(v_a_2551_, 1);
                    if v_isShared_2554_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2553_, 0, v_a_2555_);
                        v___x_2557_ = v___x_2553_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2558_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2555_);
                        v___x_2557_ = v_reuseFailAlloc_2558_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2553_);
                    v_a_2559_ = crate::leanh::lean_ctor_get(v_a_2551_, 0);
                    crate::leanh::lean_inc(v_a_2559_);
                    crate::leanh::lean_dec_ref_known(v_a_2551_, 1);
                    v_a_2537_ = v_a_2559_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_2557_;
            }
            4 => {
                if v_isShared_2565_ == 0 {
                    v___x_2567_ = v___x_2564_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2568_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2562_);
                    v___x_2567_ = v_reuseFailAlloc_2568_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2567_;
            }
            6 => {
                if v_isShared_2592_ == 0 {
                    v___x_2594_ = v___x_2591_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2595_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
                    v___x_2594_ = v_reuseFailAlloc_2595_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2594_;
            }
            8 => {
                if v_isShared_2600_ == 0 {
                    v___x_2602_ = v___x_2599_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2603_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_a_2597_);
                    v___x_2602_ = v_reuseFailAlloc_2603_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2602_;
            }
            10 => {
                if v_isShared_2610_ == 0 {
                    v___x_2612_ = v___x_2609_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2613_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
                    v___x_2612_ = v_reuseFailAlloc_2613_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2612_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___boxed(
    mut v_a_2617_: *mut crate::leanh::LeanObject,
    mut v___y_2618_: *mut crate::leanh::LeanObject,
    mut v___y_2619_: *mut crate::leanh::LeanObject,
    mut v___y_2620_: *mut crate::leanh::LeanObject,
    mut v___y_2621_: *mut crate::leanh::LeanObject,
    mut v___y_2622_: *mut crate::leanh::LeanObject,
    mut v___y_2623_: *mut crate::leanh::LeanObject,
    mut v___y_2624_: *mut crate::leanh::LeanObject,
    mut v___y_2625_: *mut crate::leanh::LeanObject,
    mut v___y_2626_: *mut crate::leanh::LeanObject,
    mut v___y_2627_: *mut crate::leanh::LeanObject,
    mut v___y_2628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2629_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg(v_a_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
    crate::leanh::lean_dec(v___y_2627_);
    crate::leanh::lean_dec_ref(v___y_2626_);
    crate::leanh::lean_dec(v___y_2625_);
    crate::leanh::lean_dec_ref(v___y_2624_);
    crate::leanh::lean_dec(v___y_2623_);
    crate::leanh::lean_dec_ref(v___y_2622_);
    crate::leanh::lean_dec(v___y_2621_);
    crate::leanh::lean_dec_ref(v___y_2620_);
    crate::leanh::lean_dec(v___y_2619_);
    crate::leanh::lean_dec(v___y_2618_);
    return v_res_2629_;
}
pub unsafe fn l_Lean_Meta_Grind_propagateBetaForNewApp(
    mut v_e_2630_: *mut crate::leanh::LeanObject,
    mut v_a_2631_: *mut crate::leanh::LeanObject,
    mut v_a_2632_: *mut crate::leanh::LeanObject,
    mut v_a_2633_: *mut crate::leanh::LeanObject,
    mut v_a_2634_: *mut crate::leanh::LeanObject,
    mut v_a_2635_: *mut crate::leanh::LeanObject,
    mut v_a_2636_: *mut crate::leanh::LeanObject,
    mut v_a_2637_: *mut crate::leanh::LeanObject,
    mut v_a_2638_: *mut crate::leanh::LeanObject,
    mut v_a_2639_: *mut crate::leanh::LeanObject,
    mut v_a_2640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2646_: u8 = 0;
    let mut v___x_2647_: u8 = 0;
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2660_: u8 = 0;
    let mut v_fst_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2670_: u8 = 0;
    let mut v_a_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2674_: u8 = 0;
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2678_: u8 = 0;
    let mut v_isSharedCheck_2679_: u8 = 0;
    let mut v_a_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2683_: u8 = 0;
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2687_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2642_ = l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget(v_e_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_);
                if crate::leanh::lean_obj_tag(v___x_2642_) == 0 {
                    v_a_2643_ = crate::leanh::lean_ctor_get(v___x_2642_, 0);
                    v_isSharedCheck_2679_ = (!crate::leanh::lean_is_exclusive(v___x_2642_)) as u8;
                    if v_isSharedCheck_2679_ == 0 {
                        v___x_2645_ = v___x_2642_;
                        v_isShared_2646_ = v_isSharedCheck_2679_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2643_);
                        crate::leanh::lean_dec(v___x_2642_);
                        v___x_2645_ = crate::leanh::lean_box(0);
                        v_isShared_2646_ = v_isSharedCheck_2679_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2630_);
                    v_a_2680_ = crate::leanh::lean_ctor_get(v___x_2642_, 0);
                    v_isSharedCheck_2687_ = (!crate::leanh::lean_is_exclusive(v___x_2642_)) as u8;
                    if v_isSharedCheck_2687_ == 0 {
                        v___x_2682_ = v___x_2642_;
                        v_isShared_2683_ = v_isSharedCheck_2687_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2680_);
                        crate::leanh::lean_dec(v___x_2642_);
                        v___x_2682_ = crate::leanh::lean_box(0);
                        v_isShared_2683_ = v_isSharedCheck_2687_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2647_ = (crate::leanh::lean_unbox(v_a_2643_) as u8);
                crate::leanh::lean_dec(v_a_2643_);
                if v___x_2647_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_2630_);
                    v___x_2648_ = crate::leanh::lean_box(0);
                    if v_isShared_2646_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2645_, 0, v___x_2648_);
                        v___x_2650_ = v___x_2645_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2651_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2648_);
                        v___x_2650_ = v_reuseFailAlloc_2651_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2645_);
                    v___x_2652_ = l_Lean_Meta_Grind_getEqcLambdas___closed__0;
                    v___x_2653_ = crate::leanh::lean_box(0);
                    v___x_2654_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2654_, 0, v_e_2630_);
                    crate::leanh::lean_ctor_set(v___x_2654_, 1, v___x_2652_);
                    v___x_2655_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2655_, 0, v___x_2653_);
                    crate::leanh::lean_ctor_set(v___x_2655_, 1, v___x_2654_);
                    v___x_2656_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg(v___x_2655_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_);
                    if crate::leanh::lean_obj_tag(v___x_2656_) == 0 {
                        v_a_2657_ = crate::leanh::lean_ctor_get(v___x_2656_, 0);
                        v_isSharedCheck_2670_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2656_)) as u8;
                        if v_isSharedCheck_2670_ == 0 {
                            v___x_2659_ = v___x_2656_;
                            v_isShared_2660_ = v_isSharedCheck_2670_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2657_);
                            crate::leanh::lean_dec(v___x_2656_);
                            v___x_2659_ = crate::leanh::lean_box(0);
                            v_isShared_2660_ = v_isSharedCheck_2670_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2671_ = crate::leanh::lean_ctor_get(v___x_2656_, 0);
                        v_isSharedCheck_2678_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2656_)) as u8;
                        if v_isSharedCheck_2678_ == 0 {
                            v___x_2673_ = v___x_2656_;
                            v_isShared_2674_ = v_isSharedCheck_2678_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2671_);
                            crate::leanh::lean_dec(v___x_2656_);
                            v___x_2673_ = crate::leanh::lean_box(0);
                            v_isShared_2674_ = v_isSharedCheck_2678_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2650_;
            }
            3 => {
                v_fst_2661_ = crate::leanh::lean_ctor_get(v_a_2657_, 0);
                crate::leanh::lean_inc(v_fst_2661_);
                crate::leanh::lean_dec(v_a_2657_);
                if crate::leanh::lean_obj_tag(v_fst_2661_) == 0 {
                    v___x_2662_ = crate::leanh::lean_box(0);
                    if v_isShared_2660_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2659_, 0, v___x_2662_);
                        v___x_2664_ = v___x_2659_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2665_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2662_);
                        v___x_2664_ = v_reuseFailAlloc_2665_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_val_2666_ = crate::leanh::lean_ctor_get(v_fst_2661_, 0);
                    crate::leanh::lean_inc(v_val_2666_);
                    crate::leanh::lean_dec_ref_known(v_fst_2661_, 1);
                    if v_isShared_2660_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2659_, 0, v_val_2666_);
                        v___x_2668_ = v___x_2659_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2669_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_val_2666_);
                        v___x_2668_ = v_reuseFailAlloc_2669_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_2664_;
            }
            5 => {
                return v___x_2668_;
            }
            6 => {
                if v_isShared_2674_ == 0 {
                    v___x_2676_ = v___x_2673_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2677_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2671_);
                    v___x_2676_ = v_reuseFailAlloc_2677_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2676_;
            }
            8 => {
                if v_isShared_2683_ == 0 {
                    v___x_2685_ = v___x_2682_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2686_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2680_);
                    v___x_2685_ = v_reuseFailAlloc_2686_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2685_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_propagateBetaForNewApp___boxed(
    mut v_e_2688_: *mut crate::leanh::LeanObject,
    mut v_a_2689_: *mut crate::leanh::LeanObject,
    mut v_a_2690_: *mut crate::leanh::LeanObject,
    mut v_a_2691_: *mut crate::leanh::LeanObject,
    mut v_a_2692_: *mut crate::leanh::LeanObject,
    mut v_a_2693_: *mut crate::leanh::LeanObject,
    mut v_a_2694_: *mut crate::leanh::LeanObject,
    mut v_a_2695_: *mut crate::leanh::LeanObject,
    mut v_a_2696_: *mut crate::leanh::LeanObject,
    mut v_a_2697_: *mut crate::leanh::LeanObject,
    mut v_a_2698_: *mut crate::leanh::LeanObject,
    mut v_a_2699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2700_ = l_Lean_Meta_Grind_propagateBetaForNewApp(
        v_e_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_,
        v_a_2696_, v_a_2697_, v_a_2698_,
    );
    crate::leanh::lean_dec(v_a_2698_);
    crate::leanh::lean_dec_ref(v_a_2697_);
    crate::leanh::lean_dec(v_a_2696_);
    crate::leanh::lean_dec_ref(v_a_2695_);
    crate::leanh::lean_dec(v_a_2694_);
    crate::leanh::lean_dec_ref(v_a_2693_);
    crate::leanh::lean_dec(v_a_2692_);
    crate::leanh::lean_dec_ref(v_a_2691_);
    crate::leanh::lean_dec(v_a_2690_);
    crate::leanh::lean_dec(v_a_2689_);
    return v_res_2700_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0(
    mut v_inst_2701_: *mut crate::leanh::LeanObject,
    mut v_a_2702_: *mut crate::leanh::LeanObject,
    mut v___y_2703_: *mut crate::leanh::LeanObject,
    mut v___y_2704_: *mut crate::leanh::LeanObject,
    mut v___y_2705_: *mut crate::leanh::LeanObject,
    mut v___y_2706_: *mut crate::leanh::LeanObject,
    mut v___y_2707_: *mut crate::leanh::LeanObject,
    mut v___y_2708_: *mut crate::leanh::LeanObject,
    mut v___y_2709_: *mut crate::leanh::LeanObject,
    mut v___y_2710_: *mut crate::leanh::LeanObject,
    mut v___y_2711_: *mut crate::leanh::LeanObject,
    mut v___y_2712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2714_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg(v_a_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
    return v___x_2714_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___boxed(
    mut v_inst_2715_: *mut crate::leanh::LeanObject,
    mut v_a_2716_: *mut crate::leanh::LeanObject,
    mut v___y_2717_: *mut crate::leanh::LeanObject,
    mut v___y_2718_: *mut crate::leanh::LeanObject,
    mut v___y_2719_: *mut crate::leanh::LeanObject,
    mut v___y_2720_: *mut crate::leanh::LeanObject,
    mut v___y_2721_: *mut crate::leanh::LeanObject,
    mut v___y_2722_: *mut crate::leanh::LeanObject,
    mut v___y_2723_: *mut crate::leanh::LeanObject,
    mut v___y_2724_: *mut crate::leanh::LeanObject,
    mut v___y_2725_: *mut crate::leanh::LeanObject,
    mut v___y_2726_: *mut crate::leanh::LeanObject,
    mut v___y_2727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2728_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0(v_inst_2715_, v_a_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
    crate::leanh::lean_dec(v___y_2726_);
    crate::leanh::lean_dec_ref(v___y_2725_);
    crate::leanh::lean_dec(v___y_2724_);
    crate::leanh::lean_dec_ref(v___y_2723_);
    crate::leanh::lean_dec(v___y_2722_);
    crate::leanh::lean_dec_ref(v___y_2721_);
    crate::leanh::lean_dec(v___y_2720_);
    crate::leanh::lean_dec_ref(v___y_2719_);
    crate::leanh::lean_dec(v___y_2718_);
    crate::leanh::lean_dec(v___y_2717_);
    return v_res_2728_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Beta(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Beta(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Beta(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Beta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Beta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Beta(builtin);
}

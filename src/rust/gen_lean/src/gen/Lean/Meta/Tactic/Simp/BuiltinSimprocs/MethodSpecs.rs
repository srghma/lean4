// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.MethodSpecs
// Imports: Init.Simproc Lean.Meta.Tactic.Simp.Simproc Lean.Meta.MethodSpecs Lean.Meta.Tactic.Simp.Main
use crate::ffi::{
    lean_array_get, lean_array_get_size, lean_array_size, lean_array_uget_borrowed, lean_mk_array,
    lean_nat_dec_eq, lean_panic_fn_borrowed, lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Simproc::{initialize_Init_Simproc, runtime_initialize_Init_Simproc};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop, l_Lean_Expr_constName_x21,
    l_Lean_Expr_getAppFn, l_Lean_Expr_isAppOfArity, l_Lean_Expr_isConst,
    l_Lean_Expr_sort___override, l_Lean_instInhabitedExpr,
};
use crate::r#gen::Lean::Meta::CtorRecognizer::l_Lean_Meta_isConstructorApp_x3f;
use crate::r#gen::Lean::Meta::MethodSpecs::{
    initialize_Lean_Meta_MethodSpecs, l_Lean_getMethodSpecTheorems,
    runtime_initialize_Lean_Meta_MethodSpecs,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Main::{
    initialize_Lean_Meta_Tactic_Simp_Main, l_Lean_Meta_Simp_instInhabitedSimpM___lam__0___boxed,
    runtime_initialize_Lean_Meta_Tactic_Simp_Main,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Rewrite::l_Lean_Meta_Simp_tryTheorem_x3f;
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpTheorems::{
    l_Lean_Meta_instInhabitedSimpTheorem_default, l_Lean_Meta_mkSimpTheoremFromConst,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Simproc::{
    initialize_Lean_Meta_Tactic_Simp_Simproc, l_Lean_Meta_Simp_registerBuiltinSimproc,
    runtime_initialize_Lean_Meta_Tactic_Simp_Simproc,
};
pub static l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Simp_instInhabitedSimpM___lam__0___boxed as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__0_value: crate::leanh::LeanStringObject<50> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 50, m_capacity: 50, m_length: 49, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 83, 105, 109, 112, 46, 66, 117, 105, 108, 116, 105, 110, 83, 105, 109, 112, 114, 111, 99, 115, 46, 77, 101, 116, 104, 111, 100, 83, 112, 101, 99, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__1_value: crate::leanh::LeanStringObject<74> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 74, m_capacity: 74, m_length: 73, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 83, 105, 109, 112, 46, 66, 117, 105, 108, 116, 105, 110, 83, 105, 109, 112, 114, 111, 99, 115, 46, 77, 101, 116, 104, 111, 100, 83, 112, 101, 99, 115, 46, 48, 46, 114, 101, 100, 117, 99, 101, 77, 101, 116, 104, 111, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__2_value: crate::leanh::LeanStringObject<44> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 115, 105, 109, 112, 84, 104, 109, 115, 46, 115, 105, 122, 101, 32, 61, 32, 49, 10, 32, 32, 32, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 2 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__3_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 2 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_reduceBEq___closed__0_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [66, 69, 113, 0],
    };
static mut l_reduceBEq___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_reduceBEq___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_reduceBEq___closed__1_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [98, 101, 113, 0],
    };
static mut l_reduceBEq___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_reduceBEq___closed__1_value) as *mut crate::leanh::LeanObject;
static l_reduceBEq___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_reduceBEq___closed__0_value) as *mut crate::leanh::LeanObject,
            16093780639914376387 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_reduceBEq___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_reduceBEq___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_reduceBEq___closed__1_value) as *mut crate::leanh::LeanObject,
            9753356465987597394 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_reduceBEq___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_reduceBEq___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13__value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [114, 101, 100, 117, 99, 101, 66, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,7878093518326082311 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_reduceBEq___closed__2_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13__value: crate::leanh::LeanArrayObject<5> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*5) as u16, other: 0, tag: 246 }, m_size: 5, m_capacity: 5, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
pub static l_reduceOrd___closed__0_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [79, 114, 100, 0],
    };
static mut l_reduceOrd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_reduceOrd___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_reduceOrd___closed__1_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [99, 111, 109, 112, 97, 114, 101, 0],
    };
static mut l_reduceOrd___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_reduceOrd___closed__1_value) as *mut crate::leanh::LeanObject;
static l_reduceOrd___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_reduceOrd___closed__0_value) as *mut crate::leanh::LeanObject,
            2238529471735800367 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_reduceOrd___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_reduceOrd___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_reduceOrd___closed__1_value) as *mut crate::leanh::LeanObject,
            7969477174634263793 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_reduceOrd___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_reduceOrd___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11__value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [114, 101, 100, 117, 99, 101, 79, 114, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11__value) as *mut crate::leanh::LeanObject,16975614873054604758 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_reduceOrd___closed__2_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11__value: crate::leanh::LeanArrayObject<5> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*5) as u16, other: 0, tag: 246 }, m_size: 5, m_capacity: 5, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11__value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0(
    mut v_msg_376_: *mut crate::leanh::LeanObject,
    mut v___y_377_: *mut crate::leanh::LeanObject,
    mut v___y_378_: *mut crate::leanh::LeanObject,
    mut v___y_379_: *mut crate::leanh::LeanObject,
    mut v___y_380_: *mut crate::leanh::LeanObject,
    mut v___y_381_: *mut crate::leanh::LeanObject,
    mut v___y_382_: *mut crate::leanh::LeanObject,
    mut v___y_383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8504__overap_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_385_ = l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0___closed__0;
    v___x_8504__overap_386_ = lean_panic_fn_borrowed(v___f_385_, v_msg_376_);
    crate::leanh::lean_inc(v___y_383_);
    crate::leanh::lean_inc_ref(v___y_382_);
    crate::leanh::lean_inc(v___y_381_);
    crate::leanh::lean_inc_ref(v___y_380_);
    crate::leanh::lean_inc(v___y_379_);
    crate::leanh::lean_inc_ref(v___y_378_);
    crate::leanh::lean_inc(v___y_377_);
    v___x_387_ = crate::leanh::lean_apply_8(
        v___x_8504__overap_386_,
        v___y_377_,
        v___y_378_,
        v___y_379_,
        v___y_380_,
        v___y_381_,
        v___y_382_,
        v___y_383_,
        crate::leanh::lean_box(0),
    );
    return v___x_387_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0___boxed(
    mut v_msg_388_: *mut crate::leanh::LeanObject,
    mut v___y_389_: *mut crate::leanh::LeanObject,
    mut v___y_390_: *mut crate::leanh::LeanObject,
    mut v___y_391_: *mut crate::leanh::LeanObject,
    mut v___y_392_: *mut crate::leanh::LeanObject,
    mut v___y_393_: *mut crate::leanh::LeanObject,
    mut v___y_394_: *mut crate::leanh::LeanObject,
    mut v___y_395_: *mut crate::leanh::LeanObject,
    mut v___y_396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_397_ = l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0(v_msg_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
    crate::leanh::lean_dec(v___y_395_);
    crate::leanh::lean_dec_ref(v___y_394_);
    crate::leanh::lean_dec(v___y_393_);
    crate::leanh::lean_dec_ref(v___y_392_);
    crate::leanh::lean_dec(v___y_391_);
    crate::leanh::lean_dec_ref(v___y_390_);
    crate::leanh::lean_dec(v___y_389_);
    return v_res_397_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__2;
    v___x_402_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_403_ = crate::leanh::lean_unsigned_to_nat(28);
    v___x_404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__1;
    v___x_405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__0;
    v___x_406_ =
        l_mkPanicMessageWithDecl(v___x_405_, v___x_404_, v___x_403_, v___x_402_, v___x_401_);
    return v___x_406_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1(
    mut v___x_410_: u8,
    mut v_e_411_: *mut crate::leanh::LeanObject,
    mut v_as_412_: *mut crate::leanh::LeanObject,
    mut v_sz_413_: usize,
    mut v_i_414_: usize,
    mut v_b_415_: *mut crate::leanh::LeanObject,
    mut v___y_416_: *mut crate::leanh::LeanObject,
    mut v___y_417_: *mut crate::leanh::LeanObject,
    mut v___y_418_: *mut crate::leanh::LeanObject,
    mut v___y_419_: *mut crate::leanh::LeanObject,
    mut v___y_420_: *mut crate::leanh::LeanObject,
    mut v___y_421_: *mut crate::leanh::LeanObject,
    mut v___y_422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: usize = 0;
    let mut v___x_427_: usize = 0;
    let mut v___x_429_: u8 = 0;
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: u8 = 0;
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: u8 = 0;
    let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_444_: u8 = 0;
    let mut v_a_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_450_: u8 = 0;
    let mut v_a_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_454_: u8 = 0;
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_458_: u8 = 0;
    let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_466_: u8 = 0;
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_471_: u8 = 0;
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_480_: u8 = 0;
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_482_: u8 = 0;
    let mut v_a_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_486_: u8 = 0;
    let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_490_: u8 = 0;
    let mut v_a_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_494_: u8 = 0;
    let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_498_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_429_ = lean_usize_dec_lt(v_i_414_, v_sz_413_);
                if v___x_429_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_411_);
                    v___x_430_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_430_, 0, v_b_415_);
                    return v___x_430_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_415_);
                    v_a_431_ = lean_array_uget_borrowed(v_as_412_, v_i_414_);
                    v___x_432_ = 0;
                    v___x_433_ = crate::leanh::lean_unsigned_to_nat(1000);
                    crate::leanh::lean_inc(v_a_431_);
                    v___x_434_ = l_Lean_Meta_mkSimpTheoremFromConst(
                        v_a_431_, v___x_410_, v___x_432_, v___x_433_, v___x_432_, v___y_419_,
                        v___y_420_, v___y_421_, v___y_422_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_434_) == 0 {
                        v_a_435_ = crate::leanh::lean_ctor_get(v___x_434_, 0);
                        crate::leanh::lean_inc(v_a_435_);
                        crate::leanh::lean_dec_ref_known(v___x_434_, 1);
                        v___x_436_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_437_ = lean_array_get_size(v_a_435_);
                        v___x_438_ = lean_nat_dec_eq(v___x_437_, v___x_436_);
                        if v___x_438_ == 0 {
                            crate::leanh::lean_dec(v_a_435_);
                            v___x_439_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__3);
                            v___x_440_ = l_panic___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__0(v___x_439_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
                            if crate::leanh::lean_obj_tag(v___x_440_) == 0 {
                                v_a_441_ = crate::leanh::lean_ctor_get(v___x_440_, 0);
                                v_isSharedCheck_450_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_440_)) as u8;
                                if v_isSharedCheck_450_ == 0 {
                                    v___x_443_ = v___x_440_;
                                    v_isShared_444_ = v_isSharedCheck_450_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_441_);
                                    crate::leanh::lean_dec(v___x_440_);
                                    v___x_443_ = crate::leanh::lean_box(0);
                                    v_isShared_444_ = v_isSharedCheck_450_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_e_411_);
                                v_a_451_ = crate::leanh::lean_ctor_get(v___x_440_, 0);
                                v_isSharedCheck_458_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_440_)) as u8;
                                if v_isSharedCheck_458_ == 0 {
                                    v___x_453_ = v___x_440_;
                                    v_isShared_454_ = v_isSharedCheck_458_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_451_);
                                    crate::leanh::lean_dec(v___x_440_);
                                    v___x_453_ = crate::leanh::lean_box(0);
                                    v_isShared_454_ = v_isSharedCheck_458_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            v___x_459_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_460_ = l_Lean_Meta_instInhabitedSimpTheorem_default;
                            v___x_461_ = lean_array_get(v___x_460_, v_a_435_, v___x_459_);
                            crate::leanh::lean_dec(v_a_435_);
                            crate::leanh::lean_inc_ref(v_e_411_);
                            v___x_462_ = l_Lean_Meta_Simp_tryTheorem_x3f(
                                v_e_411_, v___x_461_, v___y_416_, v___y_417_, v___y_418_,
                                v___y_419_, v___y_420_, v___y_421_, v___y_422_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_462_) == 0 {
                                v_a_463_ = crate::leanh::lean_ctor_get(v___x_462_, 0);
                                v_isSharedCheck_482_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_462_)) as u8;
                                if v_isSharedCheck_482_ == 0 {
                                    v___x_465_ = v___x_462_;
                                    v_isShared_466_ = v_isSharedCheck_482_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_463_);
                                    crate::leanh::lean_dec(v___x_462_);
                                    v___x_465_ = crate::leanh::lean_box(0);
                                    v_isShared_466_ = v_isSharedCheck_482_;
                                    state = 6;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_e_411_);
                                v_a_483_ = crate::leanh::lean_ctor_get(v___x_462_, 0);
                                v_isSharedCheck_490_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_462_)) as u8;
                                if v_isSharedCheck_490_ == 0 {
                                    v___x_485_ = v___x_462_;
                                    v_isShared_486_ = v_isSharedCheck_490_;
                                    state = 10;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_483_);
                                    crate::leanh::lean_dec(v___x_462_);
                                    v___x_485_ = crate::leanh::lean_box(0);
                                    v_isShared_486_ = v_isSharedCheck_490_;
                                    state = 10;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_411_);
                        v_a_491_ = crate::leanh::lean_ctor_get(v___x_434_, 0);
                        v_isSharedCheck_498_ = (!crate::leanh::lean_is_exclusive(v___x_434_)) as u8;
                        if v_isSharedCheck_498_ == 0 {
                            v___x_493_ = v___x_434_;
                            v_isShared_494_ = v_isSharedCheck_498_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_491_);
                            crate::leanh::lean_dec(v___x_434_);
                            v___x_493_ = crate::leanh::lean_box(0);
                            v_isShared_494_ = v_isSharedCheck_498_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_426_ = 1usize;
                v___x_427_ = lean_usize_add(v_i_414_, v___x_426_);
                v_i_414_ = v___x_427_;
                v_b_415_ = v_a_425_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_441_) == 0 {
                    crate::leanh::lean_dec_ref(v_e_411_);
                    v_a_445_ = crate::leanh::lean_ctor_get(v_a_441_, 0);
                    crate::leanh::lean_inc(v_a_445_);
                    crate::leanh::lean_dec_ref_known(v_a_441_, 1);
                    if v_isShared_444_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_443_, 0, v_a_445_);
                        v___x_447_ = v___x_443_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_448_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_445_);
                        v___x_447_ = v_reuseFailAlloc_448_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_443_);
                    v_a_449_ = crate::leanh::lean_ctor_get(v_a_441_, 0);
                    crate::leanh::lean_inc(v_a_449_);
                    crate::leanh::lean_dec_ref_known(v_a_441_, 1);
                    v_a_425_ = v_a_449_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                return v___x_447_;
            }
            4 => {
                if v_isShared_454_ == 0 {
                    v___x_456_ = v___x_453_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_457_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
                    v___x_456_ = v_reuseFailAlloc_457_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_456_;
            }
            6 => {
                v___x_467_ = crate::leanh::lean_box(0);
                if crate::leanh::lean_obj_tag(v_a_463_) == 1 {
                    crate::leanh::lean_dec_ref(v_e_411_);
                    v_val_468_ = crate::leanh::lean_ctor_get(v_a_463_, 0);
                    v_isSharedCheck_480_ = (!crate::leanh::lean_is_exclusive(v_a_463_)) as u8;
                    if v_isSharedCheck_480_ == 0 {
                        v___x_470_ = v_a_463_;
                        v_isShared_471_ = v_isSharedCheck_480_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_468_);
                        crate::leanh::lean_dec(v_a_463_);
                        v___x_470_ = crate::leanh::lean_box(0);
                        v_isShared_471_ = v_isSharedCheck_480_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_465_);
                    crate::leanh::lean_dec(v_a_463_);
                    v___x_481_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__4;
                    v_a_425_ = v___x_481_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                v___x_472_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_472_, 0, v_val_468_);
                if v_isShared_471_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_470_, 0, v___x_472_);
                    v___x_474_ = v___x_470_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_479_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_472_);
                    v___x_474_ = v_reuseFailAlloc_479_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_475_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_475_, 0, v___x_474_);
                crate::leanh::lean_ctor_set(v___x_475_, 1, v___x_467_);
                if v_isShared_466_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_465_, 0, v___x_475_);
                    v___x_477_ = v___x_465_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_478_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
                    v___x_477_ = v_reuseFailAlloc_478_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_477_;
            }
            10 => {
                if v_isShared_486_ == 0 {
                    v___x_488_ = v___x_485_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_489_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
                    v___x_488_ = v_reuseFailAlloc_489_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_488_;
            }
            12 => {
                if v_isShared_494_ == 0 {
                    v___x_496_ = v___x_493_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_497_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
                    v___x_496_ = v_reuseFailAlloc_497_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_496_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___boxed(
    mut v___x_499_: *mut crate::leanh::LeanObject,
    mut v_e_500_: *mut crate::leanh::LeanObject,
    mut v_as_501_: *mut crate::leanh::LeanObject,
    mut v_sz_502_: *mut crate::leanh::LeanObject,
    mut v_i_503_: *mut crate::leanh::LeanObject,
    mut v_b_504_: *mut crate::leanh::LeanObject,
    mut v___y_505_: *mut crate::leanh::LeanObject,
    mut v___y_506_: *mut crate::leanh::LeanObject,
    mut v___y_507_: *mut crate::leanh::LeanObject,
    mut v___y_508_: *mut crate::leanh::LeanObject,
    mut v___y_509_: *mut crate::leanh::LeanObject,
    mut v___y_510_: *mut crate::leanh::LeanObject,
    mut v___y_511_: *mut crate::leanh::LeanObject,
    mut v___y_512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9322__boxed_513_: u8 = 0;
    let mut v_sz_boxed_514_: usize = 0;
    let mut v_i_boxed_515_: usize = 0;
    let mut v_res_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9322__boxed_513_ = (crate::leanh::lean_unbox(v___x_499_) as u8);
    v_sz_boxed_514_ = crate::leanh::lean_unbox_usize(v_sz_502_);
    crate::leanh::lean_dec(v_sz_502_);
    v_i_boxed_515_ = crate::leanh::lean_unbox_usize(v_i_503_);
    crate::leanh::lean_dec(v_i_503_);
    v_res_516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1(v___x_9322__boxed_513_, v_e_500_, v_as_501_, v_sz_boxed_514_, v_i_boxed_515_, v_b_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
    crate::leanh::lean_dec(v___y_511_);
    crate::leanh::lean_dec_ref(v___y_510_);
    crate::leanh::lean_dec(v___y_509_);
    crate::leanh::lean_dec_ref(v___y_508_);
    crate::leanh::lean_dec(v___y_507_);
    crate::leanh::lean_dec_ref(v___y_506_);
    crate::leanh::lean_dec(v___y_505_);
    crate::leanh::lean_dec_ref(v_as_501_);
    return v_res_516_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_517_ = crate::leanh::lean_box(0);
    v_dummy_518_ = l_Lean_Expr_sort___override(v___x_517_);
    return v_dummy_518_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v_dummy_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dummy_519_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__0_once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__0);
    v___x_520_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_521_ = lean_mk_array(v___x_520_, v_dummy_519_);
    return v___x_521_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod(
    mut v_opName_526_: *mut crate::leanh::LeanObject,
    mut v_e_527_: *mut crate::leanh::LeanObject,
    mut v_a_528_: *mut crate::leanh::LeanObject,
    mut v_a_529_: *mut crate::leanh::LeanObject,
    mut v_a_530_: *mut crate::leanh::LeanObject,
    mut v_a_531_: *mut crate::leanh::LeanObject,
    mut v_a_532_: *mut crate::leanh::LeanObject,
    mut v_a_533_: *mut crate::leanh::LeanObject,
    mut v_a_534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inst_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: u8 = 0;
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_552_: u8 = 0;
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_559_: u8 = 0;
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_565_: u8 = 0;
    let mut v_val_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_568_: usize = 0;
    let mut v___x_569_: usize = 0;
    let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_574_: u8 = 0;
    let mut v_fst_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_584_: u8 = 0;
    let mut v_a_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_588_: u8 = 0;
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_592_: u8 = 0;
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_597_: u8 = 0;
    let mut v_a_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_601_: u8 = 0;
    let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_605_: u8 = 0;
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_610_: u8 = 0;
    let mut v_a_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_614_: u8 = 0;
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_618_: u8 = 0;
    let mut v___x_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_623_: u8 = 0;
    let mut v_a_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_627_: u8 = 0;
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_631_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_536_ = l_Lean_instInhabitedExpr;
                v___x_537_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_538_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__1_once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__1);
                crate::leanh::lean_inc_ref(v_e_527_);
                v_xs_539_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(
                    v___x_537_, v_e_527_, v___x_538_,
                );
                v___x_540_ = crate::leanh::lean_unsigned_to_nat(0);
                v_inst_541_ = lean_array_get(v___x_536_, v_xs_539_, v___x_540_);
                v___x_542_ = l_Lean_Expr_getAppFn(v_inst_541_);
                crate::leanh::lean_dec(v_inst_541_);
                v___x_543_ = l_Lean_Expr_isConst(v___x_542_);
                if v___x_543_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_542_);
                    crate::leanh::lean_dec_ref(v_xs_539_);
                    crate::leanh::lean_dec_ref(v_e_527_);
                    crate::leanh::lean_dec_ref(v_opName_526_);
                    v___x_544_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__2;
                    v___x_545_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_545_, 0, v___x_544_);
                    return v___x_545_;
                } else {
                    v___x_546_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_lhs_547_ = lean_array_get(v___x_536_, v_xs_539_, v___x_546_);
                    v___x_548_ = l_Lean_Meta_isConstructorApp_x3f(
                        v_lhs_547_, v_a_531_, v_a_532_, v_a_533_, v_a_534_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_548_) == 0 {
                        v_a_549_ = crate::leanh::lean_ctor_get(v___x_548_, 0);
                        v_isSharedCheck_623_ = (!crate::leanh::lean_is_exclusive(v___x_548_)) as u8;
                        if v_isSharedCheck_623_ == 0 {
                            v___x_551_ = v___x_548_;
                            v_isShared_552_ = v_isSharedCheck_623_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_549_);
                            crate::leanh::lean_dec(v___x_548_);
                            v___x_551_ = crate::leanh::lean_box(0);
                            v_isShared_552_ = v_isSharedCheck_623_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_542_);
                        crate::leanh::lean_dec_ref(v_xs_539_);
                        crate::leanh::lean_dec_ref(v_e_527_);
                        crate::leanh::lean_dec_ref(v_opName_526_);
                        v_a_624_ = crate::leanh::lean_ctor_get(v___x_548_, 0);
                        v_isSharedCheck_631_ = (!crate::leanh::lean_is_exclusive(v___x_548_)) as u8;
                        if v_isSharedCheck_631_ == 0 {
                            v___x_626_ = v___x_548_;
                            v_isShared_627_ = v_isSharedCheck_631_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_624_);
                            crate::leanh::lean_dec(v___x_548_);
                            v___x_626_ = crate::leanh::lean_box(0);
                            v_isShared_627_ = v_isSharedCheck_631_;
                            state = 16;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_549_) == 1 {
                    crate::leanh::lean_dec_ref_known(v_a_549_, 1);
                    crate::leanh::lean_del_object(v___x_551_);
                    v___x_553_ = crate::leanh::lean_unsigned_to_nat(2);
                    v_rhs_554_ = lean_array_get(v___x_536_, v_xs_539_, v___x_553_);
                    crate::leanh::lean_dec_ref(v_xs_539_);
                    v___x_555_ = l_Lean_Meta_isConstructorApp_x3f(
                        v_rhs_554_, v_a_531_, v_a_532_, v_a_533_, v_a_534_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_555_) == 0 {
                        v_a_556_ = crate::leanh::lean_ctor_get(v___x_555_, 0);
                        v_isSharedCheck_610_ = (!crate::leanh::lean_is_exclusive(v___x_555_)) as u8;
                        if v_isSharedCheck_610_ == 0 {
                            v___x_558_ = v___x_555_;
                            v_isShared_559_ = v_isSharedCheck_610_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_556_);
                            crate::leanh::lean_dec(v___x_555_);
                            v___x_558_ = crate::leanh::lean_box(0);
                            v_isShared_559_ = v_isSharedCheck_610_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_542_);
                        crate::leanh::lean_dec_ref(v_e_527_);
                        crate::leanh::lean_dec_ref(v_opName_526_);
                        v_a_611_ = crate::leanh::lean_ctor_get(v___x_555_, 0);
                        v_isSharedCheck_618_ = (!crate::leanh::lean_is_exclusive(v___x_555_)) as u8;
                        if v_isSharedCheck_618_ == 0 {
                            v___x_613_ = v___x_555_;
                            v_isShared_614_ = v_isSharedCheck_618_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_611_);
                            crate::leanh::lean_dec(v___x_555_);
                            v___x_613_ = crate::leanh::lean_box(0);
                            v_isShared_614_ = v_isSharedCheck_618_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_549_);
                    crate::leanh::lean_dec_ref(v___x_542_);
                    crate::leanh::lean_dec_ref(v_xs_539_);
                    crate::leanh::lean_dec_ref(v_e_527_);
                    crate::leanh::lean_dec_ref(v_opName_526_);
                    v___x_619_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__2;
                    if v_isShared_552_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_551_, 0, v___x_619_);
                        v___x_621_ = v___x_551_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_622_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_619_);
                        v___x_621_ = v_reuseFailAlloc_622_;
                        state = 15;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_556_) == 1 {
                    crate::leanh::lean_dec_ref_known(v_a_556_, 1);
                    crate::leanh::lean_del_object(v___x_558_);
                    v___x_560_ = l_Lean_Expr_constName_x21(v___x_542_);
                    crate::leanh::lean_dec_ref(v___x_542_);
                    v___x_561_ = l_Lean_getMethodSpecTheorems(
                        v___x_560_,
                        v_opName_526_,
                        v_a_531_,
                        v_a_532_,
                        v_a_533_,
                        v_a_534_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_561_) == 0 {
                        v_a_562_ = crate::leanh::lean_ctor_get(v___x_561_, 0);
                        v_isSharedCheck_597_ = (!crate::leanh::lean_is_exclusive(v___x_561_)) as u8;
                        if v_isSharedCheck_597_ == 0 {
                            v___x_564_ = v___x_561_;
                            v_isShared_565_ = v_isSharedCheck_597_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_562_);
                            crate::leanh::lean_dec(v___x_561_);
                            v___x_564_ = crate::leanh::lean_box(0);
                            v_isShared_565_ = v_isSharedCheck_597_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_527_);
                        v_a_598_ = crate::leanh::lean_ctor_get(v___x_561_, 0);
                        v_isSharedCheck_605_ = (!crate::leanh::lean_is_exclusive(v___x_561_)) as u8;
                        if v_isSharedCheck_605_ == 0 {
                            v___x_600_ = v___x_561_;
                            v_isShared_601_ = v_isSharedCheck_605_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_598_);
                            crate::leanh::lean_dec(v___x_561_);
                            v___x_600_ = crate::leanh::lean_box(0);
                            v_isShared_601_ = v_isSharedCheck_605_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_556_);
                    crate::leanh::lean_dec_ref(v___x_542_);
                    crate::leanh::lean_dec_ref(v_e_527_);
                    crate::leanh::lean_dec_ref(v_opName_526_);
                    v___x_606_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__2;
                    if v_isShared_559_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_558_, 0, v___x_606_);
                        v___x_608_ = v___x_558_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_609_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
                        v___x_608_ = v_reuseFailAlloc_609_;
                        state = 12;
                        continue;
                    }
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_562_) == 1 {
                    crate::leanh::lean_del_object(v___x_564_);
                    v_val_566_ = crate::leanh::lean_ctor_get(v_a_562_, 0);
                    crate::leanh::lean_inc(v_val_566_);
                    crate::leanh::lean_dec_ref_known(v_a_562_, 1);
                    v___x_567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1___closed__4;
                    v_sz_568_ = lean_array_size(v_val_566_);
                    v___x_569_ = 0usize;
                    v___x_570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod_spec__1(v___x_543_, v_e_527_, v_val_566_, v_sz_568_, v___x_569_, v___x_567_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_);
                    crate::leanh::lean_dec(v_val_566_);
                    if crate::leanh::lean_obj_tag(v___x_570_) == 0 {
                        v_a_571_ = crate::leanh::lean_ctor_get(v___x_570_, 0);
                        v_isSharedCheck_584_ = (!crate::leanh::lean_is_exclusive(v___x_570_)) as u8;
                        if v_isSharedCheck_584_ == 0 {
                            v___x_573_ = v___x_570_;
                            v_isShared_574_ = v_isSharedCheck_584_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_571_);
                            crate::leanh::lean_dec(v___x_570_);
                            v___x_573_ = crate::leanh::lean_box(0);
                            v_isShared_574_ = v_isSharedCheck_584_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_585_ = crate::leanh::lean_ctor_get(v___x_570_, 0);
                        v_isSharedCheck_592_ = (!crate::leanh::lean_is_exclusive(v___x_570_)) as u8;
                        if v_isSharedCheck_592_ == 0 {
                            v___x_587_ = v___x_570_;
                            v_isShared_588_ = v_isSharedCheck_592_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_585_);
                            crate::leanh::lean_dec(v___x_570_);
                            v___x_587_ = crate::leanh::lean_box(0);
                            v_isShared_588_ = v_isSharedCheck_592_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_562_);
                    crate::leanh::lean_dec_ref(v_e_527_);
                    v___x_593_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__2;
                    if v_isShared_565_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_564_, 0, v___x_593_);
                        v___x_595_ = v___x_564_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_596_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_593_);
                        v___x_595_ = v_reuseFailAlloc_596_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_575_ = crate::leanh::lean_ctor_get(v_a_571_, 0);
                crate::leanh::lean_inc(v_fst_575_);
                crate::leanh::lean_dec(v_a_571_);
                if crate::leanh::lean_obj_tag(v_fst_575_) == 0 {
                    v___x_576_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__3;
                    if v_isShared_574_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_573_, 0, v___x_576_);
                        v___x_578_ = v___x_573_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_579_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
                        v___x_578_ = v_reuseFailAlloc_579_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_val_580_ = crate::leanh::lean_ctor_get(v_fst_575_, 0);
                    crate::leanh::lean_inc(v_val_580_);
                    crate::leanh::lean_dec_ref_known(v_fst_575_, 1);
                    if v_isShared_574_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_573_, 0, v_val_580_);
                        v___x_582_ = v___x_573_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_583_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_583_, 0, v_val_580_);
                        v___x_582_ = v_reuseFailAlloc_583_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_578_;
            }
            6 => {
                return v___x_582_;
            }
            7 => {
                if v_isShared_588_ == 0 {
                    v___x_590_ = v___x_587_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_591_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
                    v___x_590_ = v_reuseFailAlloc_591_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_590_;
            }
            9 => {
                return v___x_595_;
            }
            10 => {
                if v_isShared_601_ == 0 {
                    v___x_603_ = v___x_600_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_604_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
                    v___x_603_ = v_reuseFailAlloc_604_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_603_;
            }
            12 => {
                return v___x_608_;
            }
            13 => {
                if v_isShared_614_ == 0 {
                    v___x_616_ = v___x_613_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_617_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_611_);
                    v___x_616_ = v_reuseFailAlloc_617_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_616_;
            }
            15 => {
                return v___x_621_;
            }
            16 => {
                if v_isShared_627_ == 0 {
                    v___x_629_ = v___x_626_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_630_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
                    v___x_629_ = v_reuseFailAlloc_630_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_629_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___boxed(
    mut v_opName_632_: *mut crate::leanh::LeanObject,
    mut v_e_633_: *mut crate::leanh::LeanObject,
    mut v_a_634_: *mut crate::leanh::LeanObject,
    mut v_a_635_: *mut crate::leanh::LeanObject,
    mut v_a_636_: *mut crate::leanh::LeanObject,
    mut v_a_637_: *mut crate::leanh::LeanObject,
    mut v_a_638_: *mut crate::leanh::LeanObject,
    mut v_a_639_: *mut crate::leanh::LeanObject,
    mut v_a_640_: *mut crate::leanh::LeanObject,
    mut v_a_641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_642_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod(
        v_opName_632_,
        v_e_633_,
        v_a_634_,
        v_a_635_,
        v_a_636_,
        v_a_637_,
        v_a_638_,
        v_a_639_,
        v_a_640_,
    );
    crate::leanh::lean_dec(v_a_640_);
    crate::leanh::lean_dec_ref(v_a_639_);
    crate::leanh::lean_dec(v_a_638_);
    crate::leanh::lean_dec_ref(v_a_637_);
    crate::leanh::lean_dec(v_a_636_);
    crate::leanh::lean_dec_ref(v_a_635_);
    crate::leanh::lean_dec(v_a_634_);
    return v_res_642_;
}
pub unsafe fn l_reduceBEq(
    mut v_e_648_: *mut crate::leanh::LeanObject,
    mut v_a_649_: *mut crate::leanh::LeanObject,
    mut v_a_650_: *mut crate::leanh::LeanObject,
    mut v_a_651_: *mut crate::leanh::LeanObject,
    mut v_a_652_: *mut crate::leanh::LeanObject,
    mut v_a_653_: *mut crate::leanh::LeanObject,
    mut v_a_654_: *mut crate::leanh::LeanObject,
    mut v_a_655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: u8 = 0;
    v___x_657_ = l_reduceBEq___closed__1;
    v___x_658_ = l_reduceBEq___closed__2;
    v___x_659_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_660_ = l_Lean_Expr_isAppOfArity(v_e_648_, v___x_658_, v___x_659_);
    if v___x_660_ == 0 {
        let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_e_648_);
        v___x_661_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__2;
        v___x_662_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_662_, 0, v___x_661_);
        return v___x_662_;
    } else {
        let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_663_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod(
            v___x_657_, v_e_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_,
            v_a_655_,
        );
        return v___x_663_;
    }
}
pub unsafe fn l_reduceBEq___boxed(
    mut v_e_664_: *mut crate::leanh::LeanObject,
    mut v_a_665_: *mut crate::leanh::LeanObject,
    mut v_a_666_: *mut crate::leanh::LeanObject,
    mut v_a_667_: *mut crate::leanh::LeanObject,
    mut v_a_668_: *mut crate::leanh::LeanObject,
    mut v_a_669_: *mut crate::leanh::LeanObject,
    mut v_a_670_: *mut crate::leanh::LeanObject,
    mut v_a_671_: *mut crate::leanh::LeanObject,
    mut v_a_672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_673_ = l_reduceBEq(
        v_e_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_,
    );
    crate::leanh::lean_dec(v_a_671_);
    crate::leanh::lean_dec_ref(v_a_670_);
    crate::leanh::lean_dec(v_a_669_);
    crate::leanh::lean_dec_ref(v_a_668_);
    crate::leanh::lean_dec(v_a_667_);
    crate::leanh::lean_dec_ref(v_a_666_);
    crate::leanh::lean_dec(v_a_665_);
    return v_res_673_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_690_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13_;
    v___x_691_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13_;
    v___x_692_ =
        crate::leanh::lean_alloc_closure(l_reduceBEq___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_693_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_690_, v___x_691_, v___x_692_);
    return v___x_693_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13____boxed(
    mut v_a_694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_695_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13_();
    return v_res_695_;
}
pub unsafe fn l_reduceOrd(
    mut v_e_701_: *mut crate::leanh::LeanObject,
    mut v_a_702_: *mut crate::leanh::LeanObject,
    mut v_a_703_: *mut crate::leanh::LeanObject,
    mut v_a_704_: *mut crate::leanh::LeanObject,
    mut v_a_705_: *mut crate::leanh::LeanObject,
    mut v_a_706_: *mut crate::leanh::LeanObject,
    mut v_a_707_: *mut crate::leanh::LeanObject,
    mut v_a_708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: u8 = 0;
    v___x_710_ = l_reduceOrd___closed__1;
    v___x_711_ = l_reduceOrd___closed__2;
    v___x_712_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_713_ = l_Lean_Expr_isAppOfArity(v_e_701_, v___x_711_, v___x_712_);
    if v___x_713_ == 0 {
        let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_e_701_);
        v___x_714_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod___closed__2;
        v___x_715_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_715_, 0, v___x_714_);
        return v___x_715_;
    } else {
        let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_716_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0__reduceMethod(
            v___x_710_, v_e_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_,
            v_a_708_,
        );
        return v___x_716_;
    }
}
pub unsafe fn l_reduceOrd___boxed(
    mut v_e_717_: *mut crate::leanh::LeanObject,
    mut v_a_718_: *mut crate::leanh::LeanObject,
    mut v_a_719_: *mut crate::leanh::LeanObject,
    mut v_a_720_: *mut crate::leanh::LeanObject,
    mut v_a_721_: *mut crate::leanh::LeanObject,
    mut v_a_722_: *mut crate::leanh::LeanObject,
    mut v_a_723_: *mut crate::leanh::LeanObject,
    mut v_a_724_: *mut crate::leanh::LeanObject,
    mut v_a_725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_726_ = l_reduceOrd(
        v_e_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_,
    );
    crate::leanh::lean_dec(v_a_724_);
    crate::leanh::lean_dec_ref(v_a_723_);
    crate::leanh::lean_dec(v_a_722_);
    crate::leanh::lean_dec_ref(v_a_721_);
    crate::leanh::lean_dec(v_a_720_);
    crate::leanh::lean_dec_ref(v_a_719_);
    crate::leanh::lean_dec(v_a_718_);
    return v_res_726_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_743_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11_;
    v___x_744_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11_;
    v___x_745_ =
        crate::leanh::lean_alloc_closure(l_reduceOrd___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_746_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_743_, v___x_744_, v___x_745_);
    return v___x_746_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11____boxed(
    mut v_a_747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_748_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11_();
    return v_res_748_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_MethodSpecs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceBEq_declare__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_2916964611____hygCtx___hyg_13_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_0____regBuiltin_reduceOrd_declare__13_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs_4114695555____hygCtx___hyg_11_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_MethodSpecs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs(builtin);
}

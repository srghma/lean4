// Lean compiler output
// Module: Lean.Compiler.LCNF.SimpCase
// Imports: Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.PassManager Lean.Compiler.LCNF.AlphaEqv Init.Omega
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_pop, lean_array_push, lean_array_size,
    lean_array_uget_borrowed, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_sub, lean_panic_fn_borrowed, lean_ptr_addr, lean_usize_add, lean_usize_dec_eq,
    lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedForall___redArg___lam__0___boxed, l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::AlphaEqv::{
    initialize_Lean_Compiler_LCNF_AlphaEqv, l_Lean_Compiler_LCNF_Code_alphaEqv,
    runtime_initialize_Lean_Compiler_LCNF_AlphaEqv,
};
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg,
    l_Lean_Compiler_LCNF_instInhabitedAlt_default__1,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    initialize_Lean_Compiler_LCNF_CompilerM,
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg,
    l_Lean_Compiler_LCNF_eraseCode___redArg, runtime_initialize_Lean_Compiler_LCNF_CompilerM,
};
use crate::r#gen::Lean::Compiler::LCNF::PassManager::{
    initialize_Lean_Compiler_LCNF_PassManager, l_Lean_Compiler_LCNF_Pass_mkPerDeclaration,
    runtime_initialize_Lean_Compiler_LCNF_PassManager,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__0_value: leanh::LeanStringObject<28> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83, 105, 109, 112, 67, 97, 115, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__1_value: leanh::LeanStringObject<72> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 72, m_capacity: 72, m_length: 71, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83, 105, 109, 112, 67, 97, 115, 101, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 97, 100, 100, 68, 101, 102, 97, 117, 108, 116, 65, 108, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__2_value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__0_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_simpCase___closed__0_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [115, 105, 109, 112, 67, 97, 115, 101, 0],
    };
static mut l_Lean_Compiler_LCNF_simpCase___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_simpCase___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_simpCase___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_simpCase___closed__0_value)
                as *mut leanh::LeanObject,
            152573878402112580 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_simpCase___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_simpCase___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_simpCase___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___boxed
            as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_simpCase___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_simpCase___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_simpCase___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_simpCase___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_simpCase: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2042452093243897853 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_simpCase___closed__0_value) as *mut leanh::LeanObject,12233630713565377370 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1501781890156459336 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4203849195465939425 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [83, 105, 109, 112, 67, 97, 115, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15170478620010304916 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,17494640641286690197 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17944010275935732608 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14737011660976769498 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,283130039692640827 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7247137155347499786 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1783459115286046307 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15595711010524809390 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5029508184210329612 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16421428518153402829 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7808061475727609480 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1808010913 as usize) << 1) | 1) as *mut leanh::LeanObject,13938647319545547308 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4295743257037208291 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1121150272219189379 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,11641711822422586182 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg(
    mut v_upperBound_1105_: *mut leanh::LeanObject,
    mut v_alts_1106_: *mut leanh::LeanObject,
    mut v_code_1107_: *mut leanh::LeanObject,
    mut v_a_1108_: *mut leanh::LeanObject,
    mut v_b_1109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1110_: u8 = 0;
    let mut v___x_1111_: u8 = 0;
    let mut v_n_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: u8 = 0;
    let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1110_ = lean_nat_dec_lt(v_a_1108_, v_upperBound_1105_);
                if v___x_1110_ == 0 {
                    leanh::lean_dec(v_a_1108_);
                    leanh::lean_dec_ref(v_code_1107_);
                    return v_b_1109_;
                } else {
                    v___x_1111_ = 1;
                    v_n_1112_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1121_ = lean_array_fget_borrowed(v_alts_1106_, v_a_1108_);
                    match leanh::lean_obj_tag(v___x_1121_) {
                        0 => {
                            v_code_1122_ = leanh::lean_ctor_get(v___x_1121_, 2);
                            leanh::lean_inc_ref(v_code_1122_);
                            v___y_1118_ = v_code_1122_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_code_1123_ = leanh::lean_ctor_get(v___x_1121_, 1);
                            leanh::lean_inc_ref(v_code_1123_);
                            v___y_1118_ = v_code_1123_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            v_code_1124_ = leanh::lean_ctor_get(v___x_1121_, 0);
                            leanh::lean_inc_ref(v_code_1124_);
                            v___y_1118_ = v_code_1124_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1115_ = lean_nat_add(v_a_1108_, v_n_1112_);
                leanh::lean_dec(v_a_1108_);
                v_a_1108_ = v___x_1115_;
                v_b_1109_ = v_a_1114_;
                state = 0;
                continue;
            }
            2 => {
                leanh::lean_inc_ref(v_code_1107_);
                v___x_1119_ =
                    l_Lean_Compiler_LCNF_Code_alphaEqv(v___x_1111_, v___y_1118_, v_code_1107_);
                if v___x_1119_ == 0 {
                    v_a_1114_ = v_b_1109_;
                    state = 1;
                    continue;
                } else {
                    v___x_1120_ = lean_nat_add(v_b_1109_, v_n_1112_);
                    leanh::lean_dec(v_b_1109_);
                    v_a_1114_ = v___x_1120_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg___boxed(
    mut v_upperBound_1125_: *mut leanh::LeanObject,
    mut v_alts_1126_: *mut leanh::LeanObject,
    mut v_code_1127_: *mut leanh::LeanObject,
    mut v_a_1128_: *mut leanh::LeanObject,
    mut v_b_1129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1130_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg(v_upperBound_1125_, v_alts_1126_, v_code_1127_, v_a_1128_, v_b_1129_);
    leanh::lean_dec_ref(v_alts_1126_);
    leanh::lean_dec(v_upperBound_1125_);
    return v_res_1130_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1131_: u8 = 0;
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1131_ = 1;
    v___x_1132_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(v___x_1131_);
    return v___x_1132_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf(
    mut v_alts_1133_: *mut leanh::LeanObject,
    mut v_i_1134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1135_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0_once), _init_l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0);
    v_n_1136_ = leanh::lean_unsigned_to_nat(1);
    v___x_1137_ = lean_nat_add(v_i_1134_, v_n_1136_);
    v___x_1138_ = lean_array_get_size(v_alts_1133_);
    v___x_1139_ = lean_array_get_borrowed(v___x_1135_, v_alts_1133_, v_i_1134_);
    match leanh::lean_obj_tag(v___x_1139_) {
        0 => {
            let mut v_code_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_code_1140_ = leanh::lean_ctor_get(v___x_1139_, 2);
            leanh::lean_inc_ref(v_code_1140_);
            v___x_1141_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg(v___x_1138_, v_alts_1133_, v_code_1140_, v___x_1137_, v_n_1136_);
            return v___x_1141_;
        }
        1 => {
            let mut v_code_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_code_1142_ = leanh::lean_ctor_get(v___x_1139_, 1);
            leanh::lean_inc_ref(v_code_1142_);
            v___x_1143_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg(v___x_1138_, v_alts_1133_, v_code_1142_, v___x_1137_, v_n_1136_);
            return v___x_1143_;
        }
        _ => {
            let mut v_code_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_code_1144_ = leanh::lean_ctor_get(v___x_1139_, 0);
            leanh::lean_inc_ref(v_code_1144_);
            v___x_1145_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg(v___x_1138_, v_alts_1133_, v_code_1144_, v___x_1137_, v_n_1136_);
            return v___x_1145_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___boxed(
    mut v_alts_1146_: *mut leanh::LeanObject,
    mut v_i_1147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1148_ =
        l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf(
            v_alts_1146_,
            v_i_1147_,
        );
    leanh::lean_dec(v_i_1147_);
    leanh::lean_dec_ref(v_alts_1146_);
    return v_res_1148_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0(
    mut v_upperBound_1149_: *mut leanh::LeanObject,
    mut v_alts_1150_: *mut leanh::LeanObject,
    mut v_code_1151_: *mut leanh::LeanObject,
    mut v_inst_1152_: *mut leanh::LeanObject,
    mut v_R_1153_: *mut leanh::LeanObject,
    mut v_a_1154_: *mut leanh::LeanObject,
    mut v_b_1155_: *mut leanh::LeanObject,
    mut v_c_1156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1157_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg(v_upperBound_1149_, v_alts_1150_, v_code_1151_, v_a_1154_, v_b_1155_);
    return v___x_1157_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___boxed(
    mut v_upperBound_1158_: *mut leanh::LeanObject,
    mut v_alts_1159_: *mut leanh::LeanObject,
    mut v_code_1160_: *mut leanh::LeanObject,
    mut v_inst_1161_: *mut leanh::LeanObject,
    mut v_R_1162_: *mut leanh::LeanObject,
    mut v_a_1163_: *mut leanh::LeanObject,
    mut v_b_1164_: *mut leanh::LeanObject,
    mut v_c_1165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1166_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0(v_upperBound_1158_, v_alts_1159_, v_code_1160_, v_inst_1161_, v_R_1162_, v_a_1163_, v_b_1164_, v_c_1165_);
    leanh::lean_dec_ref(v_alts_1159_);
    leanh::lean_dec(v_upperBound_1158_);
    return v_res_1166_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___redArg(
    mut v_upperBound_1167_: *mut leanh::LeanObject,
    mut v_alts_1168_: *mut leanh::LeanObject,
    mut v_a_1169_: *mut leanh::LeanObject,
    mut v_b_1170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: u8 = 0;
    let mut v_fst_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1181_: u8 = 0;
    let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: u8 = 0;
    let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1191_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1176_ = lean_nat_dec_lt(v_a_1169_, v_upperBound_1167_);
                if v___x_1176_ == 0 {
                    leanh::lean_dec(v_a_1169_);
                    return v_b_1170_;
                } else {
                    v_fst_1177_ = leanh::lean_ctor_get(v_b_1170_, 0);
                    v_snd_1178_ = leanh::lean_ctor_get(v_b_1170_, 1);
                    v_isSharedCheck_1191_ = (!leanh::lean_is_exclusive(v_b_1170_)) as u8;
                    if v_isSharedCheck_1191_ == 0 {
                        v___x_1180_ = v_b_1170_;
                        v_isShared_1181_ = v_isSharedCheck_1191_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1178_);
                        leanh::lean_inc(v_fst_1177_);
                        leanh::lean_dec(v_b_1170_);
                        v___x_1180_ = leanh::lean_box(0);
                        v_isShared_1181_ = v_isSharedCheck_1191_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1173_ = leanh::lean_unsigned_to_nat(1);
                v___x_1174_ = lean_nat_add(v_a_1169_, v___x_1173_);
                leanh::lean_dec(v_a_1169_);
                v_a_1169_ = v___x_1174_;
                v_b_1170_ = v_a_1172_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1182_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf(v_alts_1168_, v_a_1169_);
                v___x_1183_ = lean_nat_dec_lt(v_snd_1178_, v___x_1182_);
                if v___x_1183_ == 0 {
                    leanh::lean_dec(v___x_1182_);
                    if v_isShared_1181_ == 0 {
                        v___x_1185_ = v___x_1180_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1186_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_fst_1177_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_snd_1178_);
                        v___x_1185_ = v_reuseFailAlloc_1186_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_snd_1178_);
                    leanh::lean_dec(v_fst_1177_);
                    v___x_1187_ = lean_array_fget_borrowed(v_alts_1168_, v_a_1169_);
                    leanh::lean_inc(v___x_1187_);
                    if v_isShared_1181_ == 0 {
                        leanh::lean_ctor_set(v___x_1180_, 1, v___x_1182_);
                        leanh::lean_ctor_set(v___x_1180_, 0, v___x_1187_);
                        v___x_1189_ = v___x_1180_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1190_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 1, v___x_1182_);
                        v___x_1189_ = v_reuseFailAlloc_1190_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v_a_1172_ = v___x_1185_;
                state = 1;
                continue;
            }
            4 => {
                v_a_1172_ = v___x_1189_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___redArg___boxed(
    mut v_upperBound_1192_: *mut leanh::LeanObject,
    mut v_alts_1193_: *mut leanh::LeanObject,
    mut v_a_1194_: *mut leanh::LeanObject,
    mut v_b_1195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1196_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___redArg(v_upperBound_1192_, v_alts_1193_, v_a_1194_, v_b_1195_);
    leanh::lean_dec_ref(v_alts_1193_);
    leanh::lean_dec(v_upperBound_1192_);
    return v_res_1196_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs(
    mut v_alts_1197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxAlt_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_max_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1210_: u8 = 0;
    let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1214_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1198_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0_once), _init_l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0);
                v___x_1199_ = leanh::lean_unsigned_to_nat(1);
                v___x_1200_ = lean_array_get_size(v_alts_1197_);
                v___x_1201_ = leanh::lean_unsigned_to_nat(0);
                v_maxAlt_1202_ = lean_array_get_borrowed(v___x_1198_, v_alts_1197_, v___x_1201_);
                v_max_1203_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf(v_alts_1197_, v___x_1201_);
                leanh::lean_inc(v_maxAlt_1202_);
                v___x_1204_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1204_, 0, v_maxAlt_1202_);
                leanh::lean_ctor_set(v___x_1204_, 1, v_max_1203_);
                v___x_1205_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___redArg(v___x_1200_, v_alts_1197_, v___x_1199_, v___x_1204_);
                v_fst_1206_ = leanh::lean_ctor_get(v___x_1205_, 0);
                v_snd_1207_ = leanh::lean_ctor_get(v___x_1205_, 1);
                v_isSharedCheck_1214_ = (!leanh::lean_is_exclusive(v___x_1205_)) as u8;
                if v_isSharedCheck_1214_ == 0 {
                    v___x_1209_ = v___x_1205_;
                    v_isShared_1210_ = v_isSharedCheck_1214_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1207_);
                    leanh::lean_inc(v_fst_1206_);
                    leanh::lean_dec(v___x_1205_);
                    v___x_1209_ = leanh::lean_box(0);
                    v_isShared_1210_ = v_isSharedCheck_1214_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1210_ == 0 {
                    v___x_1212_ = v___x_1209_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1213_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_fst_1206_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_snd_1207_);
                    v___x_1212_ = v_reuseFailAlloc_1213_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1212_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs___boxed(
    mut v_alts_1215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1216_ =
        l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs(v_alts_1215_);
    leanh::lean_dec_ref(v_alts_1215_);
    return v_res_1216_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0(
    mut v_upperBound_1217_: *mut leanh::LeanObject,
    mut v_alts_1218_: *mut leanh::LeanObject,
    mut v_inst_1219_: *mut leanh::LeanObject,
    mut v_R_1220_: *mut leanh::LeanObject,
    mut v_a_1221_: *mut leanh::LeanObject,
    mut v_b_1222_: *mut leanh::LeanObject,
    mut v_c_1223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1224_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___redArg(v_upperBound_1217_, v_alts_1218_, v_a_1221_, v_b_1222_);
    return v___x_1224_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___boxed(
    mut v_upperBound_1225_: *mut leanh::LeanObject,
    mut v_alts_1226_: *mut leanh::LeanObject,
    mut v_inst_1227_: *mut leanh::LeanObject,
    mut v_R_1228_: *mut leanh::LeanObject,
    mut v_a_1229_: *mut leanh::LeanObject,
    mut v_b_1230_: *mut leanh::LeanObject,
    mut v_c_1231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1232_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0(v_upperBound_1225_, v_alts_1226_, v_inst_1227_, v_R_1228_, v_a_1229_, v_b_1230_, v_c_1231_);
    leanh::lean_dec_ref(v_alts_1226_);
    leanh::lean_dec(v_upperBound_1225_);
    return v_res_1232_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1233_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_1233_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0(
    mut v_msg_1236_: *mut leanh::LeanObject,
    mut v___y_1237_: *mut leanh::LeanObject,
    mut v___y_1238_: *mut leanh::LeanObject,
    mut v___y_1239_: *mut leanh::LeanObject,
    mut v___y_1240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1247_: u8 = 0;
    let mut v_toFunctor_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1254_: u8 = 0;
    let mut v___f_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330__overap_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1275_: u8 = 0;
    let mut v_unused_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1277_: u8 = 0;
    let mut v_unused_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1242_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__0);
                v___x_1243_ = l_StateRefT_x27_instMonad___redArg(v___x_1242_);
                v_toApplicative_1244_ = leanh::lean_ctor_get(v___x_1243_, 0);
                v_isSharedCheck_1277_ = (!leanh::lean_is_exclusive(v___x_1243_)) as u8;
                if v_isSharedCheck_1277_ == 0 {
                    v_unused_1278_ = leanh::lean_ctor_get(v___x_1243_, 1);
                    leanh::lean_dec(v_unused_1278_);
                    v___x_1246_ = v___x_1243_;
                    v_isShared_1247_ = v_isSharedCheck_1277_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_1244_);
                    leanh::lean_dec(v___x_1243_);
                    v___x_1246_ = leanh::lean_box(0);
                    v_isShared_1247_ = v_isSharedCheck_1277_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1248_ = leanh::lean_ctor_get(v_toApplicative_1244_, 0);
                v_toSeq_1249_ = leanh::lean_ctor_get(v_toApplicative_1244_, 2);
                v_toSeqLeft_1250_ = leanh::lean_ctor_get(v_toApplicative_1244_, 3);
                v_toSeqRight_1251_ = leanh::lean_ctor_get(v_toApplicative_1244_, 4);
                v_isSharedCheck_1275_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_1244_)) as u8;
                if v_isSharedCheck_1275_ == 0 {
                    v_unused_1276_ = leanh::lean_ctor_get(v_toApplicative_1244_, 1);
                    leanh::lean_dec(v_unused_1276_);
                    v___x_1253_ = v_toApplicative_1244_;
                    v_isShared_1254_ = v_isSharedCheck_1275_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_1251_);
                    leanh::lean_inc(v_toSeqLeft_1250_);
                    leanh::lean_inc(v_toSeq_1249_);
                    leanh::lean_inc(v_toFunctor_1248_);
                    leanh::lean_dec(v_toApplicative_1244_);
                    v___x_1253_ = leanh::lean_box(0);
                    v_isShared_1254_ = v_isSharedCheck_1275_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1255_ = l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__1;
                v___f_1256_ = l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__2;
                leanh::lean_inc_ref(v_toFunctor_1248_);
                v___f_1257_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1257_, 0, v_toFunctor_1248_);
                v___f_1258_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1258_, 0, v_toFunctor_1248_);
                v___x_1259_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1259_, 0, v___f_1257_);
                leanh::lean_ctor_set(v___x_1259_, 1, v___f_1258_);
                v___f_1260_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1260_, 0, v_toSeqRight_1251_);
                v___f_1261_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1261_, 0, v_toSeqLeft_1250_);
                v___f_1262_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1262_, 0, v_toSeq_1249_);
                if v_isShared_1254_ == 0 {
                    leanh::lean_ctor_set(v___x_1253_, 4, v___f_1260_);
                    leanh::lean_ctor_set(v___x_1253_, 3, v___f_1261_);
                    leanh::lean_ctor_set(v___x_1253_, 2, v___f_1262_);
                    leanh::lean_ctor_set(v___x_1253_, 1, v___f_1255_);
                    leanh::lean_ctor_set(v___x_1253_, 0, v___x_1259_);
                    v___x_1264_ = v___x_1253_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1274_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1259_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1274_, 1, v___f_1255_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1274_, 2, v___f_1262_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1274_, 3, v___f_1261_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1274_, 4, v___f_1260_);
                    v___x_1264_ = v_reuseFailAlloc_1274_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1247_ == 0 {
                    leanh::lean_ctor_set(v___x_1246_, 1, v___f_1256_);
                    leanh::lean_ctor_set(v___x_1246_, 0, v___x_1264_);
                    v___x_1266_ = v___x_1246_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1273_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1264_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1273_, 1, v___f_1256_);
                    v___x_1266_ = v_reuseFailAlloc_1273_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1267_ = l_StateRefT_x27_instMonad___redArg(v___x_1266_);
                v___x_1268_ = leanh::lean_box(0);
                v___x_1269_ = l_instInhabitedOfMonad___redArg(v___x_1267_, v___x_1268_);
                v___f_1270_ = leanh::lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_1270_, 0, v___x_1269_);
                v___x_2330__overap_1271_ = lean_panic_fn_borrowed(v___f_1270_, v_msg_1236_);
                leanh::lean_dec_ref(v___f_1270_);
                leanh::lean_inc(v___y_1240_);
                leanh::lean_inc_ref(v___y_1239_);
                leanh::lean_inc(v___y_1238_);
                leanh::lean_inc_ref(v___y_1237_);
                v___x_1272_ = leanh::lean_apply_5(
                    v___x_2330__overap_1271_,
                    v___y_1237_,
                    v___y_1238_,
                    v___y_1239_,
                    v___y_1240_,
                    leanh::lean_box(0),
                );
                return v___x_1272_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___boxed(
    mut v_msg_1279_: *mut leanh::LeanObject,
    mut v___y_1280_: *mut leanh::LeanObject,
    mut v___y_1281_: *mut leanh::LeanObject,
    mut v___y_1282_: *mut leanh::LeanObject,
    mut v___y_1283_: *mut leanh::LeanObject,
    mut v___y_1284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1285_ = l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0(v_msg_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
    leanh::lean_dec(v___y_1283_);
    leanh::lean_dec_ref(v___y_1282_);
    leanh::lean_dec(v___y_1281_);
    leanh::lean_dec_ref(v___y_1280_);
    return v_res_1285_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__2;
    v___x_1290_ = leanh::lean_unsigned_to_nat(36);
    v___x_1291_ = leanh::lean_unsigned_to_nat(77);
    v___x_1292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__1;
    v___x_1293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__0;
    v___x_1294_ = l_mkPanicMessageWithDecl(
        v___x_1293_,
        v___x_1292_,
        v___x_1291_,
        v___x_1290_,
        v___x_1289_,
    );
    return v___x_1294_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1(
    mut v_snd_1295_: *mut leanh::LeanObject,
    mut v_fst_1296_: *mut leanh::LeanObject,
    mut v_as_1297_: *mut leanh::LeanObject,
    mut v_sz_1298_: usize,
    mut v_i_1299_: usize,
    mut v_b_1300_: *mut leanh::LeanObject,
    mut v___y_1301_: *mut leanh::LeanObject,
    mut v___y_1302_: *mut leanh::LeanObject,
    mut v___y_1303_: *mut leanh::LeanObject,
    mut v___y_1304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: usize = 0;
    let mut v___x_1309_: usize = 0;
    let mut v___x_1311_: u8 = 0;
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1317_: u8 = 0;
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: u8 = 0;
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: u8 = 0;
    let mut v___y_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: u8 = 0;
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: u8 = 0;
    let mut v_code_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1339_: u8 = 0;
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1343_: u8 = 0;
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1350_: u8 = 0;
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1354_: u8 = 0;
    let mut v___y_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1363_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1311_ = lean_usize_dec_lt(v_i_1299_, v_sz_1298_);
                if v___x_1311_ == 0 {
                    leanh::lean_dec_ref(v_fst_1296_);
                    v___x_1312_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1312_, 0, v_b_1300_);
                    return v___x_1312_;
                } else {
                    v_fst_1313_ = leanh::lean_ctor_get(v_b_1300_, 0);
                    v_snd_1314_ = leanh::lean_ctor_get(v_b_1300_, 1);
                    v_isSharedCheck_1363_ = (!leanh::lean_is_exclusive(v_b_1300_)) as u8;
                    if v_isSharedCheck_1363_ == 0 {
                        v___x_1316_ = v_b_1300_;
                        v_isShared_1317_ = v_isSharedCheck_1363_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1314_);
                        leanh::lean_inc(v_fst_1313_);
                        leanh::lean_dec(v_b_1300_);
                        v___x_1316_ = leanh::lean_box(0);
                        v_isShared_1317_ = v_isSharedCheck_1363_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1308_ = 1usize;
                v___x_1309_ = lean_usize_add(v_i_1299_, v___x_1308_);
                v_i_1299_ = v___x_1309_;
                v_b_1300_ = v_a_1307_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1318_ = leanh::lean_unsigned_to_nat(1);
                v___x_1319_ = lean_nat_dec_eq(v_snd_1295_, v___x_1318_);
                v_a_1325_ = lean_array_uget_borrowed(v_as_1297_, v_i_1299_);
                v___x_1326_ = 1;
                match leanh::lean_obj_tag(v_a_1325_) {
                    0 => {
                        v_code_1360_ = leanh::lean_ctor_get(v_a_1325_, 2);
                        leanh::lean_inc_ref(v_code_1360_);
                        v___y_1356_ = v_code_1360_;
                        state = 10;
                        continue;
                    }
                    1 => {
                        v_code_1361_ = leanh::lean_ctor_get(v_a_1325_, 1);
                        leanh::lean_inc_ref(v_code_1361_);
                        v___y_1356_ = v_code_1361_;
                        state = 10;
                        continue;
                    }
                    _ => {
                        v_code_1362_ = leanh::lean_ctor_get(v_a_1325_, 0);
                        leanh::lean_inc_ref(v_code_1362_);
                        v___y_1356_ = v_code_1362_;
                        state = 10;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1321_ = leanh::lean_box((v___x_1319_) as usize);
                if v_isShared_1317_ == 0 {
                    leanh::lean_ctor_set(v___x_1316_, 1, v___x_1321_);
                    v___x_1323_ = v___x_1316_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1324_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_fst_1313_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1324_, 1, v___x_1321_);
                    v___x_1323_ = v_reuseFailAlloc_1324_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_1307_ = v___x_1323_;
                state = 1;
                continue;
            }
            5 => {
                v___x_1330_ =
                    l_Lean_Compiler_LCNF_Code_alphaEqv(v___x_1326_, v___y_1328_, v___y_1329_);
                if v___x_1330_ == 0 {
                    leanh::lean_del_object(v___x_1316_);
                    leanh::lean_inc(v_a_1325_);
                    v___x_1331_ = lean_array_push(v_fst_1313_, v_a_1325_);
                    v___x_1332_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1332_, 0, v___x_1331_);
                    leanh::lean_ctor_set(v___x_1332_, 1, v_snd_1314_);
                    v_a_1307_ = v___x_1332_;
                    state = 1;
                    continue;
                } else {
                    if leanh::lean_obj_tag(v_a_1325_) == 1 {
                        v___x_1333_ = (leanh::lean_unbox(v_snd_1314_) as u8);
                        leanh::lean_dec(v_snd_1314_);
                        if v___x_1333_ == 0 {
                            v_code_1334_ = leanh::lean_ctor_get(v_a_1325_, 1);
                            v___x_1335_ = l_Lean_Compiler_LCNF_eraseCode___redArg(
                                v___x_1326_,
                                v_code_1334_,
                                v___y_1302_,
                            );
                            if leanh::lean_obj_tag(v___x_1335_) == 0 {
                                leanh::lean_dec_ref_known(v___x_1335_, 1);
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_del_object(v___x_1316_);
                                leanh::lean_dec(v_fst_1313_);
                                leanh::lean_dec_ref(v_fst_1296_);
                                v_a_1336_ = leanh::lean_ctor_get(v___x_1335_, 0);
                                v_isSharedCheck_1343_ =
                                    (!leanh::lean_is_exclusive(v___x_1335_)) as u8;
                                if v_isSharedCheck_1343_ == 0 {
                                    v___x_1338_ = v___x_1335_;
                                    v_isShared_1339_ = v_isSharedCheck_1343_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1336_);
                                    leanh::lean_dec(v___x_1335_);
                                    v___x_1338_ = leanh::lean_box(0);
                                    v_isShared_1339_ = v_isSharedCheck_1343_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1316_);
                        v___x_1344_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3);
                        v___x_1345_ = l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0(v___x_1344_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
                        if leanh::lean_obj_tag(v___x_1345_) == 0 {
                            leanh::lean_dec_ref_known(v___x_1345_, 1);
                            v___x_1346_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1346_, 0, v_fst_1313_);
                            leanh::lean_ctor_set(v___x_1346_, 1, v_snd_1314_);
                            v_a_1307_ = v___x_1346_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_snd_1314_);
                            leanh::lean_dec(v_fst_1313_);
                            leanh::lean_dec_ref(v_fst_1296_);
                            v_a_1347_ = leanh::lean_ctor_get(v___x_1345_, 0);
                            v_isSharedCheck_1354_ =
                                (!leanh::lean_is_exclusive(v___x_1345_)) as u8;
                            if v_isSharedCheck_1354_ == 0 {
                                v___x_1349_ = v___x_1345_;
                                v_isShared_1350_ = v_isSharedCheck_1354_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1347_);
                                leanh::lean_dec(v___x_1345_);
                                v___x_1349_ = leanh::lean_box(0);
                                v_isShared_1350_ = v_isSharedCheck_1354_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                }
            }
            6 => {
                if v_isShared_1339_ == 0 {
                    v___x_1341_ = v___x_1338_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1342_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
                    v___x_1341_ = v_reuseFailAlloc_1342_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1341_;
            }
            8 => {
                if v_isShared_1350_ == 0 {
                    v___x_1352_ = v___x_1349_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1353_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
                    v___x_1352_ = v_reuseFailAlloc_1353_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1352_;
            }
            10 => match leanh::lean_obj_tag(v_fst_1296_) {
                0 => {
                    v_code_1357_ = leanh::lean_ctor_get(v_fst_1296_, 2);
                    leanh::lean_inc_ref(v_code_1357_);
                    v___y_1328_ = v___y_1356_;
                    v___y_1329_ = v_code_1357_;
                    state = 5;
                    continue;
                }
                1 => {
                    v_code_1358_ = leanh::lean_ctor_get(v_fst_1296_, 1);
                    leanh::lean_inc_ref(v_code_1358_);
                    v___y_1328_ = v___y_1356_;
                    v___y_1329_ = v_code_1358_;
                    state = 5;
                    continue;
                }
                _ => {
                    v_code_1359_ = leanh::lean_ctor_get(v_fst_1296_, 0);
                    leanh::lean_inc_ref(v_code_1359_);
                    v___y_1328_ = v___y_1356_;
                    v___y_1329_ = v_code_1359_;
                    state = 5;
                    continue;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___boxed(
    mut v_snd_1364_: *mut leanh::LeanObject,
    mut v_fst_1365_: *mut leanh::LeanObject,
    mut v_as_1366_: *mut leanh::LeanObject,
    mut v_sz_1367_: *mut leanh::LeanObject,
    mut v_i_1368_: *mut leanh::LeanObject,
    mut v_b_1369_: *mut leanh::LeanObject,
    mut v___y_1370_: *mut leanh::LeanObject,
    mut v___y_1371_: *mut leanh::LeanObject,
    mut v___y_1372_: *mut leanh::LeanObject,
    mut v___y_1373_: *mut leanh::LeanObject,
    mut v___y_1374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1375_: usize = 0;
    let mut v_i_boxed_1376_: usize = 0;
    let mut v_res_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1375_ = leanh::lean_unbox_usize(v_sz_1367_);
    leanh::lean_dec(v_sz_1367_);
    v_i_boxed_1376_ = leanh::lean_unbox_usize(v_i_1368_);
    leanh::lean_dec(v_i_1368_);
    v_res_1377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1(v_snd_1364_, v_fst_1365_, v_as_1366_, v_sz_boxed_1375_, v_i_boxed_1376_, v_b_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
    leanh::lean_dec(v___y_1373_);
    leanh::lean_dec_ref(v___y_1372_);
    leanh::lean_dec(v___y_1371_);
    leanh::lean_dec_ref(v___y_1370_);
    leanh::lean_dec_ref(v_as_1366_);
    leanh::lean_dec(v_snd_1364_);
    return v_res_1377_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__2(
    mut v___x_1378_: *mut leanh::LeanObject,
    mut v_as_1379_: *mut leanh::LeanObject,
    mut v_i_1380_: usize,
    mut v_stop_1381_: usize,
) -> u8 {
    let mut v___x_1382_: u8 = 0;
    let mut v___x_1383_: u8 = 0;
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: u8 = 0;
    let mut v___x_1387_: usize = 0;
    let mut v___x_1388_: usize = 0;
    let mut v___x_1390_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1382_ = lean_usize_dec_eq(v_i_1380_, v_stop_1381_);
                if v___x_1382_ == 0 {
                    v___x_1383_ = 1;
                    v___x_1384_ = lean_array_uget_borrowed(v_as_1379_, v_i_1380_);
                    if leanh::lean_obj_tag(v___x_1384_) == 2 {
                        return v___x_1383_;
                    } else {
                        v___x_1385_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1386_ = lean_nat_dec_le(v___x_1378_, v___x_1385_);
                        if v___x_1386_ == 0 {
                            v___x_1387_ = 1usize;
                            v___x_1388_ = lean_usize_add(v_i_1380_, v___x_1387_);
                            v_i_1380_ = v___x_1388_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_1383_;
                        }
                    }
                } else {
                    v___x_1390_ = 0;
                    return v___x_1390_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__2___boxed(
    mut v___x_1391_: *mut leanh::LeanObject,
    mut v_as_1392_: *mut leanh::LeanObject,
    mut v_i_1393_: *mut leanh::LeanObject,
    mut v_stop_1394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1395_: usize = 0;
    let mut v_stop_boxed_1396_: usize = 0;
    let mut v_res_1397_: u8 = 0;
    let mut v_r_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1395_ = leanh::lean_unbox_usize(v_i_1393_);
    leanh::lean_dec(v_i_1393_);
    v_stop_boxed_1396_ = leanh::lean_unbox_usize(v_stop_1394_);
    leanh::lean_dec(v_stop_1394_);
    v_res_1397_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__2(v___x_1391_, v_as_1392_, v_i_boxed_1395_, v_stop_boxed_1396_);
    leanh::lean_dec_ref(v_as_1392_);
    leanh::lean_dec(v___x_1391_);
    v_r_1398_ = leanh::lean_box((v_res_1397_) as usize);
    return v_r_1398_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt(
    mut v_alts_1405_: *mut leanh::LeanObject,
    mut v_a_1406_: *mut leanh::LeanObject,
    mut v_a_1407_: *mut leanh::LeanObject,
    mut v_a_1408_: *mut leanh::LeanObject,
    mut v_a_1409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1420_: u8 = 0;
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: u8 = 0;
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1426_: usize = 0;
    let mut v___x_1427_: usize = 0;
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1439_: u8 = 0;
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1443_: u8 = 0;
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: u8 = 0;
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: u8 = 0;
    let mut v___x_1449_: usize = 0;
    let mut v___x_1450_: usize = 0;
    let mut v___x_1451_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1417_ = lean_array_get_size(v_alts_1405_);
                v___x_1418_ = leanh::lean_unsigned_to_nat(1);
                v___x_1446_ = lean_nat_dec_le(v___x_1417_, v___x_1418_);
                if v___x_1446_ == 0 {
                    v___x_1447_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1448_ = lean_nat_dec_lt(v___x_1447_, v___x_1417_);
                    if v___x_1448_ == 0 {
                        v___y_1420_ = v___x_1446_;
                        state = 2;
                        continue;
                    } else {
                        if v___x_1448_ == 0 {
                            v___y_1420_ = v___x_1446_;
                            state = 2;
                            continue;
                        } else {
                            v___x_1449_ = 0usize;
                            v___x_1450_ = lean_usize_of_nat(v___x_1417_);
                            v___x_1451_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__2(v___x_1417_, v_alts_1405_, v___x_1449_, v___x_1450_);
                            v___y_1420_ = v___x_1451_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___y_1420_ = v___x_1446_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1414_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1414_, 0, v___y_1413_);
                v___x_1415_ = lean_array_push(v___y_1412_, v___x_1414_);
                v___x_1416_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1416_, 0, v___x_1415_);
                return v___x_1416_;
            }
            2 => {
                if v___y_1420_ == 0 {
                    v___x_1421_ =
                        l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs(
                            v_alts_1405_,
                        );
                    v_fst_1422_ = leanh::lean_ctor_get(v___x_1421_, 0);
                    leanh::lean_inc(v_fst_1422_);
                    v_snd_1423_ = leanh::lean_ctor_get(v___x_1421_, 1);
                    leanh::lean_inc(v_snd_1423_);
                    leanh::lean_dec_ref(v___x_1421_);
                    v___x_1424_ = lean_nat_dec_eq(v_snd_1423_, v___x_1418_);
                    if v___x_1424_ == 0 {
                        v___x_1425_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__1;
                        v_sz_1426_ = lean_array_size(v_alts_1405_);
                        v___x_1427_ = 0usize;
                        leanh::lean_inc(v_fst_1422_);
                        v___x_1428_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1(v_snd_1423_, v_fst_1422_, v_alts_1405_, v_sz_1426_, v___x_1427_, v___x_1425_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_);
                        leanh::lean_dec_ref(v_alts_1405_);
                        leanh::lean_dec(v_snd_1423_);
                        if leanh::lean_obj_tag(v___x_1428_) == 0 {
                            v_a_1429_ = leanh::lean_ctor_get(v___x_1428_, 0);
                            leanh::lean_inc(v_a_1429_);
                            leanh::lean_dec_ref_known(v___x_1428_, 1);
                            match leanh::lean_obj_tag(v_fst_1422_) {
                                0 => {
                                    v_fst_1430_ = leanh::lean_ctor_get(v_a_1429_, 0);
                                    leanh::lean_inc(v_fst_1430_);
                                    leanh::lean_dec(v_a_1429_);
                                    v_code_1431_ = leanh::lean_ctor_get(v_fst_1422_, 2);
                                    leanh::lean_inc_ref(v_code_1431_);
                                    leanh::lean_dec_ref_known(v_fst_1422_, 3);
                                    v___y_1412_ = v_fst_1430_;
                                    v___y_1413_ = v_code_1431_;
                                    state = 1;
                                    continue;
                                }
                                1 => {
                                    v_fst_1432_ = leanh::lean_ctor_get(v_a_1429_, 0);
                                    leanh::lean_inc(v_fst_1432_);
                                    leanh::lean_dec(v_a_1429_);
                                    v_code_1433_ = leanh::lean_ctor_get(v_fst_1422_, 1);
                                    leanh::lean_inc_ref(v_code_1433_);
                                    leanh::lean_dec_ref_known(v_fst_1422_, 2);
                                    v___y_1412_ = v_fst_1432_;
                                    v___y_1413_ = v_code_1433_;
                                    state = 1;
                                    continue;
                                }
                                _ => {
                                    v_fst_1434_ = leanh::lean_ctor_get(v_a_1429_, 0);
                                    leanh::lean_inc(v_fst_1434_);
                                    leanh::lean_dec(v_a_1429_);
                                    v_code_1435_ = leanh::lean_ctor_get(v_fst_1422_, 0);
                                    leanh::lean_inc_ref(v_code_1435_);
                                    leanh::lean_dec_ref_known(v_fst_1422_, 1);
                                    v___y_1412_ = v_fst_1434_;
                                    v___y_1413_ = v_code_1435_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_fst_1422_);
                            v_a_1436_ = leanh::lean_ctor_get(v___x_1428_, 0);
                            v_isSharedCheck_1443_ =
                                (!leanh::lean_is_exclusive(v___x_1428_)) as u8;
                            if v_isSharedCheck_1443_ == 0 {
                                v___x_1438_ = v___x_1428_;
                                v_isShared_1439_ = v_isSharedCheck_1443_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1436_);
                                leanh::lean_dec(v___x_1428_);
                                v___x_1438_ = leanh::lean_box(0);
                                v_isShared_1439_ = v_isSharedCheck_1443_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_snd_1423_);
                        leanh::lean_dec(v_fst_1422_);
                        v___x_1444_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1444_, 0, v_alts_1405_);
                        return v___x_1444_;
                    }
                } else {
                    v___x_1445_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1445_, 0, v_alts_1405_);
                    return v___x_1445_;
                }
            }
            3 => {
                if v_isShared_1439_ == 0 {
                    v___x_1441_ = v___x_1438_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1442_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
                    v___x_1441_ = v_reuseFailAlloc_1442_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1441_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___boxed(
    mut v_alts_1452_: *mut leanh::LeanObject,
    mut v_a_1453_: *mut leanh::LeanObject,
    mut v_a_1454_: *mut leanh::LeanObject,
    mut v_a_1455_: *mut leanh::LeanObject,
    mut v_a_1456_: *mut leanh::LeanObject,
    mut v_a_1457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1458_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt(
        v_alts_1452_,
        v_a_1453_,
        v_a_1454_,
        v_a_1455_,
        v_a_1456_,
    );
    leanh::lean_dec(v_a_1456_);
    leanh::lean_dec_ref(v_a_1455_);
    leanh::lean_dec(v_a_1454_);
    leanh::lean_dec_ref(v_a_1453_);
    return v_res_1458_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0(
    mut v_as_1459_: *mut leanh::LeanObject,
    mut v_i_1460_: usize,
    mut v_stop_1461_: usize,
    mut v_b_1462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: usize = 0;
    let mut v___x_1466_: usize = 0;
    let mut v___x_1468_: u8 = 0;
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1468_ = lean_usize_dec_eq(v_i_1460_, v_stop_1461_);
                if v___x_1468_ == 0 {
                    v___x_1469_ = lean_array_uget_borrowed(v_as_1459_, v_i_1460_);
                    match leanh::lean_obj_tag(v___x_1469_) {
                        0 => {
                            v_code_1473_ = leanh::lean_ctor_get(v___x_1469_, 2);
                            leanh::lean_inc_ref(v_code_1473_);
                            v___y_1471_ = v_code_1473_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_code_1474_ = leanh::lean_ctor_get(v___x_1469_, 1);
                            leanh::lean_inc_ref(v_code_1474_);
                            v___y_1471_ = v_code_1474_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            v_code_1475_ = leanh::lean_ctor_get(v___x_1469_, 0);
                            leanh::lean_inc_ref(v_code_1475_);
                            v___y_1471_ = v_code_1475_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    return v_b_1462_;
                }
            }
            1 => {
                v___x_1465_ = 1usize;
                v___x_1466_ = lean_usize_add(v_i_1460_, v___x_1465_);
                v_i_1460_ = v___x_1466_;
                v_b_1462_ = v___y_1464_;
                state = 0;
                continue;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_1471_) == 6 {
                    leanh::lean_dec_ref_known(v___y_1471_, 1);
                    v___y_1464_ = v_b_1462_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_1471_);
                    leanh::lean_inc(v___x_1469_);
                    v___x_1472_ = lean_array_push(v_b_1462_, v___x_1469_);
                    v___y_1464_ = v___x_1472_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0___boxed(
    mut v_as_1476_: *mut leanh::LeanObject,
    mut v_i_1477_: *mut leanh::LeanObject,
    mut v_stop_1478_: *mut leanh::LeanObject,
    mut v_b_1479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1480_: usize = 0;
    let mut v_stop_boxed_1481_: usize = 0;
    let mut v_res_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1480_ = leanh::lean_unbox_usize(v_i_1477_);
    leanh::lean_dec(v_i_1477_);
    v_stop_boxed_1481_ = leanh::lean_unbox_usize(v_stop_1478_);
    leanh::lean_dec(v_stop_1478_);
    v_res_1482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0(v_as_1476_, v_i_boxed_1480_, v_stop_boxed_1481_, v_b_1479_);
    leanh::lean_dec_ref(v_as_1476_);
    return v_res_1482_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable(
    mut v_alts_1483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: u8 = 0;
    v___x_1484_ = leanh::lean_unsigned_to_nat(0);
    v___x_1485_ = lean_array_get_size(v_alts_1483_);
    v___x_1486_ =
        l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__0;
    v___x_1487_ = lean_nat_dec_lt(v___x_1484_, v___x_1485_);
    if v___x_1487_ == 0 {
        return v___x_1486_;
    } else {
        let mut v___x_1488_: u8 = 0;
        v___x_1488_ = lean_nat_dec_le(v___x_1485_, v___x_1485_);
        if v___x_1488_ == 0 {
            if v___x_1487_ == 0 {
                return v___x_1486_;
            } else {
                let mut v___x_1489_: usize = 0;
                let mut v___x_1490_: usize = 0;
                let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1489_ = 0usize;
                v___x_1490_ = lean_usize_of_nat(v___x_1485_);
                v___x_1491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0(v_alts_1483_, v___x_1489_, v___x_1490_, v___x_1486_);
                return v___x_1491_;
            }
        } else {
            let mut v___x_1492_: usize = 0;
            let mut v___x_1493_: usize = 0;
            let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1492_ = 0usize;
            v___x_1493_ = lean_usize_of_nat(v___x_1485_);
            v___x_1494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0(v_alts_1483_, v___x_1492_, v___x_1493_, v___x_1486_);
            return v___x_1494_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable___boxed(
    mut v_alts_1495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1496_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable(
        v_alts_1495_,
    );
    leanh::lean_dec_ref(v_alts_1495_);
    return v_res_1496_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases(
    mut v_c_1497_: *mut leanh::LeanObject,
    mut v_a_1498_: *mut leanh::LeanObject,
    mut v_a_1499_: *mut leanh::LeanObject,
    mut v_a_1500_: *mut leanh::LeanObject,
    mut v_a_1501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_typeName_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1509_: u8 = 0;
    let mut v_alts_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1515_: u8 = 0;
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: u8 = 0;
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: u8 = 0;
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1545_: u8 = 0;
    let mut v_a_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1549_: u8 = 0;
    let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1553_: u8 = 0;
    let mut v_isSharedCheck_1554_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_typeName_1503_ = leanh::lean_ctor_get(v_c_1497_, 0);
                v_resultType_1504_ = leanh::lean_ctor_get(v_c_1497_, 1);
                v_discr_1505_ = leanh::lean_ctor_get(v_c_1497_, 2);
                v_alts_1506_ = leanh::lean_ctor_get(v_c_1497_, 3);
                v_isSharedCheck_1554_ = (!leanh::lean_is_exclusive(v_c_1497_)) as u8;
                if v_isSharedCheck_1554_ == 0 {
                    v___x_1508_ = v_c_1497_;
                    v_isShared_1509_ = v_isSharedCheck_1554_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_alts_1506_);
                    leanh::lean_inc(v_discr_1505_);
                    leanh::lean_inc(v_resultType_1504_);
                    leanh::lean_inc(v_typeName_1503_);
                    leanh::lean_dec(v_c_1497_);
                    v___x_1508_ = leanh::lean_box(0);
                    v_isShared_1509_ = v_isSharedCheck_1554_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_alts_1510_ =
                    l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable(
                        v_alts_1506_,
                    );
                leanh::lean_dec_ref(v_alts_1506_);
                v___x_1511_ =
                    l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt(
                        v_alts_1510_,
                        v_a_1498_,
                        v_a_1499_,
                        v_a_1500_,
                        v_a_1501_,
                    );
                if leanh::lean_obj_tag(v___x_1511_) == 0 {
                    v_a_1512_ = leanh::lean_ctor_get(v___x_1511_, 0);
                    v_isSharedCheck_1545_ = (!leanh::lean_is_exclusive(v___x_1511_)) as u8;
                    if v_isSharedCheck_1545_ == 0 {
                        v___x_1514_ = v___x_1511_;
                        v_isShared_1515_ = v_isSharedCheck_1545_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1512_);
                        leanh::lean_dec(v___x_1511_);
                        v___x_1514_ = leanh::lean_box(0);
                        v_isShared_1515_ = v_isSharedCheck_1545_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1508_);
                    leanh::lean_dec(v_discr_1505_);
                    leanh::lean_dec_ref(v_resultType_1504_);
                    leanh::lean_dec(v_typeName_1503_);
                    v_a_1546_ = leanh::lean_ctor_get(v___x_1511_, 0);
                    v_isSharedCheck_1553_ = (!leanh::lean_is_exclusive(v___x_1511_)) as u8;
                    if v_isSharedCheck_1553_ == 0 {
                        v___x_1548_ = v___x_1511_;
                        v_isShared_1549_ = v_isSharedCheck_1553_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1546_);
                        leanh::lean_dec(v___x_1511_);
                        v___x_1548_ = leanh::lean_box(0);
                        v_isShared_1549_ = v_isSharedCheck_1553_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1516_ = lean_array_get_size(v_a_1512_);
                v___x_1517_ = leanh::lean_unsigned_to_nat(0);
                v___x_1518_ = lean_nat_dec_eq(v___x_1516_, v___x_1517_);
                if v___x_1518_ == 0 {
                    v___x_1519_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1520_ = lean_nat_dec_eq(v___x_1516_, v___x_1519_);
                    if v___x_1520_ == 0 {
                        if v_isShared_1509_ == 0 {
                            leanh::lean_ctor_set(v___x_1508_, 3, v_a_1512_);
                            v___x_1522_ = v___x_1508_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1527_ =
                                leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1527_,
                                0,
                                v_typeName_1503_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1527_,
                                1,
                                v_resultType_1504_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 2, v_discr_1505_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 3, v_a_1512_);
                            v___x_1522_ = v_reuseFailAlloc_1527_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1508_);
                        leanh::lean_dec(v_discr_1505_);
                        leanh::lean_dec_ref(v_resultType_1504_);
                        leanh::lean_dec(v_typeName_1503_);
                        v___x_1528_ = lean_array_fget(v_a_1512_, v___x_1517_);
                        leanh::lean_dec(v_a_1512_);
                        match leanh::lean_obj_tag(v___x_1528_) {
                            0 => {
                                v_code_1529_ = leanh::lean_ctor_get(v___x_1528_, 2);
                                leanh::lean_inc_ref(v_code_1529_);
                                leanh::lean_dec_ref_known(v___x_1528_, 3);
                                if v_isShared_1515_ == 0 {
                                    leanh::lean_ctor_set(v___x_1514_, 0, v_code_1529_);
                                    v___x_1531_ = v___x_1514_;
                                    state = 5;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1532_ =
                                        leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1532_,
                                        0,
                                        v_code_1529_,
                                    );
                                    v___x_1531_ = v_reuseFailAlloc_1532_;
                                    state = 5;
                                    continue;
                                }
                            }
                            1 => {
                                v_code_1533_ = leanh::lean_ctor_get(v___x_1528_, 1);
                                leanh::lean_inc_ref(v_code_1533_);
                                leanh::lean_dec_ref_known(v___x_1528_, 2);
                                if v_isShared_1515_ == 0 {
                                    leanh::lean_ctor_set(v___x_1514_, 0, v_code_1533_);
                                    v___x_1535_ = v___x_1514_;
                                    state = 6;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1536_ =
                                        leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1536_,
                                        0,
                                        v_code_1533_,
                                    );
                                    v___x_1535_ = v_reuseFailAlloc_1536_;
                                    state = 6;
                                    continue;
                                }
                            }
                            _ => {
                                v_code_1537_ = leanh::lean_ctor_get(v___x_1528_, 0);
                                leanh::lean_inc_ref(v_code_1537_);
                                leanh::lean_dec_ref_known(v___x_1528_, 1);
                                if v_isShared_1515_ == 0 {
                                    leanh::lean_ctor_set(v___x_1514_, 0, v_code_1537_);
                                    v___x_1539_ = v___x_1514_;
                                    state = 7;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1540_ =
                                        leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1540_,
                                        0,
                                        v_code_1537_,
                                    );
                                    v___x_1539_ = v_reuseFailAlloc_1540_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_1512_);
                    leanh::lean_del_object(v___x_1508_);
                    leanh::lean_dec(v_discr_1505_);
                    leanh::lean_dec(v_typeName_1503_);
                    v___x_1541_ = leanh::lean_alloc_ctor(6, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1541_, 0, v_resultType_1504_);
                    if v_isShared_1515_ == 0 {
                        leanh::lean_ctor_set(v___x_1514_, 0, v___x_1541_);
                        v___x_1543_ = v___x_1514_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1544_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
                        v___x_1543_ = v_reuseFailAlloc_1544_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1523_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1523_, 0, v___x_1522_);
                if v_isShared_1515_ == 0 {
                    leanh::lean_ctor_set(v___x_1514_, 0, v___x_1523_);
                    v___x_1525_ = v___x_1514_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1526_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1523_);
                    v___x_1525_ = v_reuseFailAlloc_1526_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1525_;
            }
            5 => {
                return v___x_1531_;
            }
            6 => {
                return v___x_1535_;
            }
            7 => {
                return v___x_1539_;
            }
            8 => {
                return v___x_1543_;
            }
            9 => {
                if v_isShared_1549_ == 0 {
                    v___x_1551_ = v___x_1548_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1552_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
                    v___x_1551_ = v_reuseFailAlloc_1552_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1551_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases___boxed(
    mut v_c_1555_: *mut leanh::LeanObject,
    mut v_a_1556_: *mut leanh::LeanObject,
    mut v_a_1557_: *mut leanh::LeanObject,
    mut v_a_1558_: *mut leanh::LeanObject,
    mut v_a_1559_: *mut leanh::LeanObject,
    mut v_a_1560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1561_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases(
        v_c_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_,
    );
    leanh::lean_dec(v_a_1559_);
    leanh::lean_dec_ref(v_a_1558_);
    leanh::lean_dec(v_a_1557_);
    leanh::lean_dec_ref(v_a_1556_);
    return v_res_1561_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg(
    mut v_alt_1562_: *mut leanh::LeanObject,
    mut v_f_1563_: *mut leanh::LeanObject,
    mut v___y_1564_: *mut leanh::LeanObject,
    mut v___y_1565_: *mut leanh::LeanObject,
    mut v___y_1566_: *mut leanh::LeanObject,
    mut v___y_1567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1575_: u8 = 0;
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1580_: u8 = 0;
    let mut v_a_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1584_: u8 = 0;
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1588_: u8 = 0;
    let mut v_code_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_alt_1562_) {
                0 => {
                    v_code_1589_ = leanh::lean_ctor_get(v_alt_1562_, 2);
                    leanh::lean_inc_ref(v_code_1589_);
                    v___y_1570_ = v_code_1589_;
                    state = 1;
                    continue;
                }
                1 => {
                    v_code_1590_ = leanh::lean_ctor_get(v_alt_1562_, 1);
                    leanh::lean_inc_ref(v_code_1590_);
                    v___y_1570_ = v_code_1590_;
                    state = 1;
                    continue;
                }
                _ => {
                    v_code_1591_ = leanh::lean_ctor_get(v_alt_1562_, 0);
                    leanh::lean_inc_ref(v_code_1591_);
                    v___y_1570_ = v_code_1591_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                leanh::lean_inc(v___y_1567_);
                leanh::lean_inc_ref(v___y_1566_);
                leanh::lean_inc(v___y_1565_);
                leanh::lean_inc_ref(v___y_1564_);
                v___x_1571_ = leanh::lean_apply_6(
                    v_f_1563_,
                    v___y_1570_,
                    v___y_1564_,
                    v___y_1565_,
                    v___y_1566_,
                    v___y_1567_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1571_) == 0 {
                    v_a_1572_ = leanh::lean_ctor_get(v___x_1571_, 0);
                    v_isSharedCheck_1580_ = (!leanh::lean_is_exclusive(v___x_1571_)) as u8;
                    if v_isSharedCheck_1580_ == 0 {
                        v___x_1574_ = v___x_1571_;
                        v_isShared_1575_ = v_isSharedCheck_1580_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1572_);
                        leanh::lean_dec(v___x_1571_);
                        v___x_1574_ = leanh::lean_box(0);
                        v_isShared_1575_ = v_isSharedCheck_1580_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_alt_1562_);
                    v_a_1581_ = leanh::lean_ctor_get(v___x_1571_, 0);
                    v_isSharedCheck_1588_ = (!leanh::lean_is_exclusive(v___x_1571_)) as u8;
                    if v_isSharedCheck_1588_ == 0 {
                        v___x_1583_ = v___x_1571_;
                        v_isShared_1584_ = v_isSharedCheck_1588_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1581_);
                        leanh::lean_dec(v___x_1571_);
                        v___x_1583_ = leanh::lean_box(0);
                        v_isShared_1584_ = v_isSharedCheck_1588_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1576_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_1562_, v_a_1572_);
                if v_isShared_1575_ == 0 {
                    leanh::lean_ctor_set(v___x_1574_, 0, v___x_1576_);
                    v___x_1578_ = v___x_1574_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1579_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
                    v___x_1578_ = v_reuseFailAlloc_1579_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1578_;
            }
            4 => {
                if v_isShared_1584_ == 0 {
                    v___x_1586_ = v___x_1583_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1587_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1581_);
                    v___x_1586_ = v_reuseFailAlloc_1587_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1586_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg___boxed(
    mut v_alt_1592_: *mut leanh::LeanObject,
    mut v_f_1593_: *mut leanh::LeanObject,
    mut v___y_1594_: *mut leanh::LeanObject,
    mut v___y_1595_: *mut leanh::LeanObject,
    mut v___y_1596_: *mut leanh::LeanObject,
    mut v___y_1597_: *mut leanh::LeanObject,
    mut v___y_1598_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1599_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg(v_alt_1592_, v_f_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
    leanh::lean_dec(v___y_1597_);
    leanh::lean_dec_ref(v___y_1596_);
    leanh::lean_dec(v___y_1595_);
    leanh::lean_dec_ref(v___y_1594_);
    return v_res_1599_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0(
    mut v_pu_1600_: u8,
    mut v_alt_1601_: *mut leanh::LeanObject,
    mut v_f_1602_: *mut leanh::LeanObject,
    mut v___y_1603_: *mut leanh::LeanObject,
    mut v___y_1604_: *mut leanh::LeanObject,
    mut v___y_1605_: *mut leanh::LeanObject,
    mut v___y_1606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1608_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg(v_alt_1601_, v_f_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
    return v___x_1608_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___boxed(
    mut v_pu_1609_: *mut leanh::LeanObject,
    mut v_alt_1610_: *mut leanh::LeanObject,
    mut v_f_1611_: *mut leanh::LeanObject,
    mut v___y_1612_: *mut leanh::LeanObject,
    mut v___y_1613_: *mut leanh::LeanObject,
    mut v___y_1614_: *mut leanh::LeanObject,
    mut v___y_1615_: *mut leanh::LeanObject,
    mut v___y_1616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1617_: u8 = 0;
    let mut v_res_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1617_ = (leanh::lean_unbox(v_pu_1609_) as u8);
    v_res_1618_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0(v_pu_boxed_1617_, v_alt_1610_, v_f_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
    leanh::lean_dec(v___y_1615_);
    leanh::lean_dec_ref(v___y_1614_);
    leanh::lean_dec(v___y_1613_);
    leanh::lean_dec_ref(v___y_1612_);
    return v_res_1618_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(
    mut v_code_1619_: *mut leanh::LeanObject,
    mut v_a_1620_: *mut leanh::LeanObject,
    mut v_a_1621_: *mut leanh::LeanObject,
    mut v_a_1622_: *mut leanh::LeanObject,
    mut v_a_1623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_decl_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1631_: u8 = 0;
    let mut v___x_1632_: usize = 0;
    let mut v___x_1633_: usize = 0;
    let mut v___x_1634_: u8 = 0;
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1637_: u8 = 0;
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1644_: u8 = 0;
    let mut v_unused_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1650_: u8 = 0;
    let mut v_decl_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: u8 = 0;
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1665_: u8 = 0;
    let mut v___y_1667_: u8 = 0;
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1670_: u8 = 0;
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1677_: u8 = 0;
    let mut v_unused_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: usize = 0;
    let mut v___x_1684_: usize = 0;
    let mut v___x_1685_: u8 = 0;
    let mut v___x_1686_: usize = 0;
    let mut v___x_1687_: usize = 0;
    let mut v___x_1688_: u8 = 0;
    let mut v_isSharedCheck_1689_: u8 = 0;
    let mut v_a_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1693_: u8 = 0;
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1697_: u8 = 0;
    let mut v_cases_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1705_: u8 = 0;
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1716_: u8 = 0;
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1720_: u8 = 0;
    let mut v_isSharedCheck_1721_: u8 = 0;
    let mut v_fvarId_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1730_: u8 = 0;
    let mut v___x_1731_: usize = 0;
    let mut v___x_1732_: usize = 0;
    let mut v___x_1733_: u8 = 0;
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1736_: u8 = 0;
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1743_: u8 = 0;
    let mut v_unused_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1751_: u8 = 0;
    let mut v_fvarId_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1760_: u8 = 0;
    let mut v___x_1761_: usize = 0;
    let mut v___x_1762_: usize = 0;
    let mut v___x_1763_: u8 = 0;
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1766_: u8 = 0;
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1773_: u8 = 0;
    let mut v_unused_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1781_: u8 = 0;
    let mut v_fvarId_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1792_: u8 = 0;
    let mut v___x_1793_: usize = 0;
    let mut v___x_1794_: usize = 0;
    let mut v___x_1795_: u8 = 0;
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1798_: u8 = 0;
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1805_: u8 = 0;
    let mut v_unused_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1815_: u8 = 0;
    let mut v_fvarId_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1823_: u8 = 0;
    let mut v___x_1824_: usize = 0;
    let mut v___x_1825_: usize = 0;
    let mut v___x_1826_: u8 = 0;
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1829_: u8 = 0;
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1836_: u8 = 0;
    let mut v_unused_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1843_: u8 = 0;
    let mut v_fvarId_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_1846_: u8 = 0;
    let mut v_persistent_1847_: u8 = 0;
    let mut v_k_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1853_: u8 = 0;
    let mut v___x_1854_: usize = 0;
    let mut v___x_1855_: usize = 0;
    let mut v___x_1856_: u8 = 0;
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1859_: u8 = 0;
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1866_: u8 = 0;
    let mut v_unused_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1873_: u8 = 0;
    let mut v_fvarId_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_1876_: u8 = 0;
    let mut v_persistent_1877_: u8 = 0;
    let mut v_objs_x3f_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1884_: u8 = 0;
    let mut v___x_1885_: usize = 0;
    let mut v___x_1886_: usize = 0;
    let mut v___x_1887_: u8 = 0;
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1890_: u8 = 0;
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1897_: u8 = 0;
    let mut v_unused_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1905_: u8 = 0;
    let mut v_fvarId_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1912_: u8 = 0;
    let mut v___x_1913_: usize = 0;
    let mut v___x_1914_: usize = 0;
    let mut v___x_1915_: u8 = 0;
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1918_: u8 = 0;
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1925_: u8 = 0;
    let mut v_unused_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1931_: u8 = 0;
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match leanh::lean_obj_tag(v_code_1619_) {
                    0 => {
                        v_decl_1625_ = leanh::lean_ctor_get(v_code_1619_, 0);
                        v_k_1626_ = leanh::lean_ctor_get(v_code_1619_, 1);
                        leanh::lean_inc_ref(v_k_1626_);
                        v___x_1627_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_1626_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
                        if leanh::lean_obj_tag(v___x_1627_) == 0 {
                            v_a_1628_ = leanh::lean_ctor_get(v___x_1627_, 0);
                            v_isSharedCheck_1650_ =
                                (!leanh::lean_is_exclusive(v___x_1627_)) as u8;
                            if v_isSharedCheck_1650_ == 0 {
                                v___x_1630_ = v___x_1627_;
                                v_isShared_1631_ = v_isSharedCheck_1650_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1628_);
                                leanh::lean_dec(v___x_1627_);
                                v___x_1630_ = leanh::lean_box(0);
                                v_isShared_1631_ = v_isSharedCheck_1650_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_code_1619_, 2);
                            return v___x_1627_;
                        }
                    }
                    2 => {
                        v_decl_1651_ = leanh::lean_ctor_get(v_code_1619_, 0);
                        v_k_1652_ = leanh::lean_ctor_get(v_code_1619_, 1);
                        v_params_1653_ = leanh::lean_ctor_get(v_decl_1651_, 2);
                        v_type_1654_ = leanh::lean_ctor_get(v_decl_1651_, 3);
                        v_value_1655_ = leanh::lean_ctor_get(v_decl_1651_, 4);
                        leanh::lean_inc_ref(v_value_1655_);
                        v___x_1656_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_value_1655_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
                        if leanh::lean_obj_tag(v___x_1656_) == 0 {
                            v_a_1657_ = leanh::lean_ctor_get(v___x_1656_, 0);
                            leanh::lean_inc(v_a_1657_);
                            leanh::lean_dec_ref_known(v___x_1656_, 1);
                            v___x_1658_ = 1;
                            leanh::lean_inc_ref(v_params_1653_);
                            leanh::lean_inc_ref(v_type_1654_);
                            leanh::lean_inc_ref(v_decl_1651_);
                            v___x_1659_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1658_, v_decl_1651_, v_type_1654_, v_params_1653_, v_a_1657_, v_a_1621_);
                            if leanh::lean_obj_tag(v___x_1659_) == 0 {
                                v_a_1660_ = leanh::lean_ctor_get(v___x_1659_, 0);
                                leanh::lean_inc(v_a_1660_);
                                leanh::lean_dec_ref_known(v___x_1659_, 1);
                                leanh::lean_inc_ref(v_k_1652_);
                                v___x_1661_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_1652_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
                                if leanh::lean_obj_tag(v___x_1661_) == 0 {
                                    v_a_1662_ = leanh::lean_ctor_get(v___x_1661_, 0);
                                    v_isSharedCheck_1689_ =
                                        (!leanh::lean_is_exclusive(v___x_1661_)) as u8;
                                    if v_isSharedCheck_1689_ == 0 {
                                        v___x_1664_ = v___x_1661_;
                                        v_isShared_1665_ = v_isSharedCheck_1689_;
                                        state = 6;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1662_);
                                        leanh::lean_dec(v___x_1661_);
                                        v___x_1664_ = leanh::lean_box(0);
                                        v_isShared_1665_ = v_isSharedCheck_1689_;
                                        state = 6;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_1660_);
                                    leanh::lean_dec_ref_known(v_code_1619_, 2);
                                    return v___x_1661_;
                                }
                            } else {
                                leanh::lean_dec_ref_known(v_code_1619_, 2);
                                v_a_1690_ = leanh::lean_ctor_get(v___x_1659_, 0);
                                v_isSharedCheck_1697_ =
                                    (!leanh::lean_is_exclusive(v___x_1659_)) as u8;
                                if v_isSharedCheck_1697_ == 0 {
                                    v___x_1692_ = v___x_1659_;
                                    v_isShared_1693_ = v_isSharedCheck_1697_;
                                    state = 12;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1690_);
                                    leanh::lean_dec(v___x_1659_);
                                    v___x_1692_ = leanh::lean_box(0);
                                    v_isShared_1693_ = v_isSharedCheck_1697_;
                                    state = 12;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_code_1619_, 2);
                            return v___x_1656_;
                        }
                    }
                    4 => {
                        v_cases_1698_ = leanh::lean_ctor_get(v_code_1619_, 0);
                        leanh::lean_inc_ref(v_cases_1698_);
                        leanh::lean_dec_ref_known(v_code_1619_, 1);
                        v_typeName_1699_ = leanh::lean_ctor_get(v_cases_1698_, 0);
                        v_resultType_1700_ = leanh::lean_ctor_get(v_cases_1698_, 1);
                        v_discr_1701_ = leanh::lean_ctor_get(v_cases_1698_, 2);
                        v_alts_1702_ = leanh::lean_ctor_get(v_cases_1698_, 3);
                        v_isSharedCheck_1721_ =
                            (!leanh::lean_is_exclusive(v_cases_1698_)) as u8;
                        if v_isSharedCheck_1721_ == 0 {
                            v___x_1704_ = v_cases_1698_;
                            v_isShared_1705_ = v_isSharedCheck_1721_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_inc(v_alts_1702_);
                            leanh::lean_inc(v_discr_1701_);
                            leanh::lean_inc(v_resultType_1700_);
                            leanh::lean_inc(v_typeName_1699_);
                            leanh::lean_dec(v_cases_1698_);
                            v___x_1704_ = leanh::lean_box(0);
                            v_isShared_1705_ = v_isSharedCheck_1721_;
                            state = 14;
                            continue;
                        }
                    }
                    7 => {
                        v_fvarId_1722_ = leanh::lean_ctor_get(v_code_1619_, 0);
                        v_i_1723_ = leanh::lean_ctor_get(v_code_1619_, 1);
                        v_y_1724_ = leanh::lean_ctor_get(v_code_1619_, 2);
                        v_k_1725_ = leanh::lean_ctor_get(v_code_1619_, 3);
                        leanh::lean_inc_ref(v_k_1725_);
                        v___x_1726_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_1725_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
                        if leanh::lean_obj_tag(v___x_1726_) == 0 {
                            v_a_1727_ = leanh::lean_ctor_get(v___x_1726_, 0);
                            v_isSharedCheck_1751_ =
                                (!leanh::lean_is_exclusive(v___x_1726_)) as u8;
                            if v_isSharedCheck_1751_ == 0 {
                                v___x_1729_ = v___x_1726_;
                                v_isShared_1730_ = v_isSharedCheck_1751_;
                                state = 18;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1727_);
                                leanh::lean_dec(v___x_1726_);
                                v___x_1729_ = leanh::lean_box(0);
                                v_isShared_1730_ = v_isSharedCheck_1751_;
                                state = 18;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_code_1619_, 4);
                            return v___x_1726_;
                        }
                    }
                    8 => {
                        v_fvarId_1752_ = leanh::lean_ctor_get(v_code_1619_, 0);
                        v_i_1753_ = leanh::lean_ctor_get(v_code_1619_, 1);
                        v_y_1754_ = leanh::lean_ctor_get(v_code_1619_, 2);
                        v_k_1755_ = leanh::lean_ctor_get(v_code_1619_, 3);
                        leanh::lean_inc_ref(v_k_1755_);
                        v___x_1756_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_1755_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
                        if leanh::lean_obj_tag(v___x_1756_) == 0 {
                            v_a_1757_ = leanh::lean_ctor_get(v___x_1756_, 0);
                            v_isSharedCheck_1781_ =
                                (!leanh::lean_is_exclusive(v___x_1756_)) as u8;
                            if v_isSharedCheck_1781_ == 0 {
                                v___x_1759_ = v___x_1756_;
                                v_isShared_1760_ = v_isSharedCheck_1781_;
                                state = 23;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1757_);
                                leanh::lean_dec(v___x_1756_);
                                v___x_1759_ = leanh::lean_box(0);
                                v_isShared_1760_ = v_isSharedCheck_1781_;
                                state = 23;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_code_1619_, 4);
                            return v___x_1756_;
                        }
                    }
                    9 => {
                        v_fvarId_1782_ = leanh::lean_ctor_get(v_code_1619_, 0);
                        v_i_1783_ = leanh::lean_ctor_get(v_code_1619_, 1);
                        v_offset_1784_ = leanh::lean_ctor_get(v_code_1619_, 2);
                        v_y_1785_ = leanh::lean_ctor_get(v_code_1619_, 3);
                        v_ty_1786_ = leanh::lean_ctor_get(v_code_1619_, 4);
                        v_k_1787_ = leanh::lean_ctor_get(v_code_1619_, 5);
                        leanh::lean_inc_ref(v_k_1787_);
                        v___x_1788_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_1787_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
                        if leanh::lean_obj_tag(v___x_1788_) == 0 {
                            v_a_1789_ = leanh::lean_ctor_get(v___x_1788_, 0);
                            v_isSharedCheck_1815_ =
                                (!leanh::lean_is_exclusive(v___x_1788_)) as u8;
                            if v_isSharedCheck_1815_ == 0 {
                                v___x_1791_ = v___x_1788_;
                                v_isShared_1792_ = v_isSharedCheck_1815_;
                                state = 28;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1789_);
                                leanh::lean_dec(v___x_1788_);
                                v___x_1791_ = leanh::lean_box(0);
                                v_isShared_1792_ = v_isSharedCheck_1815_;
                                state = 28;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_code_1619_, 6);
                            return v___x_1788_;
                        }
                    }
                    10 => {
                        v_fvarId_1816_ = leanh::lean_ctor_get(v_code_1619_, 0);
                        v_cidx_1817_ = leanh::lean_ctor_get(v_code_1619_, 1);
                        v_k_1818_ = leanh::lean_ctor_get(v_code_1619_, 2);
                        leanh::lean_inc_ref(v_k_1818_);
                        v___x_1819_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_1818_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
                        if leanh::lean_obj_tag(v___x_1819_) == 0 {
                            v_a_1820_ = leanh::lean_ctor_get(v___x_1819_, 0);
                            v_isSharedCheck_1843_ =
                                (!leanh::lean_is_exclusive(v___x_1819_)) as u8;
                            if v_isSharedCheck_1843_ == 0 {
                                v___x_1822_ = v___x_1819_;
                                v_isShared_1823_ = v_isSharedCheck_1843_;
                                state = 33;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1820_);
                                leanh::lean_dec(v___x_1819_);
                                v___x_1822_ = leanh::lean_box(0);
                                v_isShared_1823_ = v_isSharedCheck_1843_;
                                state = 33;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_code_1619_, 3);
                            return v___x_1819_;
                        }
                    }
                    11 => {
                        v_fvarId_1844_ = leanh::lean_ctor_get(v_code_1619_, 0);
                        v_n_1845_ = leanh::lean_ctor_get(v_code_1619_, 1);
                        v_check_1846_ = leanh::lean_ctor_get_uint8(
                            v_code_1619_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        );
                        v_persistent_1847_ = leanh::lean_ctor_get_uint8(
                            v_code_1619_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                        );
                        v_k_1848_ = leanh::lean_ctor_get(v_code_1619_, 2);
                        leanh::lean_inc_ref(v_k_1848_);
                        v___x_1849_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_1848_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
                        if leanh::lean_obj_tag(v___x_1849_) == 0 {
                            v_a_1850_ = leanh::lean_ctor_get(v___x_1849_, 0);
                            v_isSharedCheck_1873_ =
                                (!leanh::lean_is_exclusive(v___x_1849_)) as u8;
                            if v_isSharedCheck_1873_ == 0 {
                                v___x_1852_ = v___x_1849_;
                                v_isShared_1853_ = v_isSharedCheck_1873_;
                                state = 38;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1850_);
                                leanh::lean_dec(v___x_1849_);
                                v___x_1852_ = leanh::lean_box(0);
                                v_isShared_1853_ = v_isSharedCheck_1873_;
                                state = 38;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_code_1619_, 3);
                            return v___x_1849_;
                        }
                    }
                    12 => {
                        v_fvarId_1874_ = leanh::lean_ctor_get(v_code_1619_, 0);
                        v_n_1875_ = leanh::lean_ctor_get(v_code_1619_, 1);
                        v_check_1876_ = leanh::lean_ctor_get_uint8(
                            v_code_1619_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        );
                        v_persistent_1877_ = leanh::lean_ctor_get_uint8(
                            v_code_1619_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
                        );
                        v_objs_x3f_1878_ = leanh::lean_ctor_get(v_code_1619_, 2);
                        v_k_1879_ = leanh::lean_ctor_get(v_code_1619_, 3);
                        leanh::lean_inc_ref(v_k_1879_);
                        v___x_1880_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_1879_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
                        if leanh::lean_obj_tag(v___x_1880_) == 0 {
                            v_a_1881_ = leanh::lean_ctor_get(v___x_1880_, 0);
                            v_isSharedCheck_1905_ =
                                (!leanh::lean_is_exclusive(v___x_1880_)) as u8;
                            if v_isSharedCheck_1905_ == 0 {
                                v___x_1883_ = v___x_1880_;
                                v_isShared_1884_ = v_isSharedCheck_1905_;
                                state = 43;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1881_);
                                leanh::lean_dec(v___x_1880_);
                                v___x_1883_ = leanh::lean_box(0);
                                v_isShared_1884_ = v_isSharedCheck_1905_;
                                state = 43;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_code_1619_, 4);
                            return v___x_1880_;
                        }
                    }
                    13 => {
                        v_fvarId_1906_ = leanh::lean_ctor_get(v_code_1619_, 0);
                        v_k_1907_ = leanh::lean_ctor_get(v_code_1619_, 1);
                        leanh::lean_inc_ref(v_k_1907_);
                        v___x_1908_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_1907_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
                        if leanh::lean_obj_tag(v___x_1908_) == 0 {
                            v_a_1909_ = leanh::lean_ctor_get(v___x_1908_, 0);
                            v_isSharedCheck_1931_ =
                                (!leanh::lean_is_exclusive(v___x_1908_)) as u8;
                            if v_isSharedCheck_1931_ == 0 {
                                v___x_1911_ = v___x_1908_;
                                v_isShared_1912_ = v_isSharedCheck_1931_;
                                state = 48;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1909_);
                                leanh::lean_dec(v___x_1908_);
                                v___x_1911_ = leanh::lean_box(0);
                                v_isShared_1912_ = v_isSharedCheck_1931_;
                                state = 48;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_code_1619_, 2);
                            return v___x_1908_;
                        }
                    }
                    _ => {
                        v___x_1932_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1932_, 0, v_code_1619_);
                        return v___x_1932_;
                    }
                }
            }
            1 => {
                v___x_1632_ = lean_ptr_addr(v_k_1626_);
                v___x_1633_ = lean_ptr_addr(v_a_1628_);
                v___x_1634_ = lean_usize_dec_eq(v___x_1632_, v___x_1633_);
                if v___x_1634_ == 0 {
                    leanh::lean_inc_ref(v_decl_1625_);
                    v_isSharedCheck_1644_ = (!leanh::lean_is_exclusive(v_code_1619_)) as u8;
                    if v_isSharedCheck_1644_ == 0 {
                        v_unused_1645_ = leanh::lean_ctor_get(v_code_1619_, 1);
                        leanh::lean_dec(v_unused_1645_);
                        v_unused_1646_ = leanh::lean_ctor_get(v_code_1619_, 0);
                        leanh::lean_dec(v_unused_1646_);
                        v___x_1636_ = v_code_1619_;
                        v_isShared_1637_ = v_isSharedCheck_1644_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_code_1619_);
                        v___x_1636_ = leanh::lean_box(0);
                        v_isShared_1637_ = v_isSharedCheck_1644_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1628_);
                    if v_isShared_1631_ == 0 {
                        leanh::lean_ctor_set(v___x_1630_, 0, v_code_1619_);
                        v___x_1648_ = v___x_1630_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1649_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_code_1619_);
                        v___x_1648_ = v_reuseFailAlloc_1649_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1637_ == 0 {
                    leanh::lean_ctor_set(v___x_1636_, 1, v_a_1628_);
                    v___x_1639_ = v___x_1636_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1643_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_decl_1625_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_a_1628_);
                    v___x_1639_ = v_reuseFailAlloc_1643_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1631_ == 0 {
                    leanh::lean_ctor_set(v___x_1630_, 0, v___x_1639_);
                    v___x_1641_ = v___x_1630_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1642_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
                    v___x_1641_ = v_reuseFailAlloc_1642_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1641_;
            }
            5 => {
                return v___x_1648_;
            }
            6 => {
                v___x_1683_ = lean_ptr_addr(v_k_1652_);
                v___x_1684_ = lean_ptr_addr(v_a_1662_);
                v___x_1685_ = lean_usize_dec_eq(v___x_1683_, v___x_1684_);
                if v___x_1685_ == 0 {
                    v___y_1667_ = v___x_1685_;
                    state = 7;
                    continue;
                } else {
                    v___x_1686_ = lean_ptr_addr(v_decl_1651_);
                    v___x_1687_ = lean_ptr_addr(v_a_1660_);
                    v___x_1688_ = lean_usize_dec_eq(v___x_1686_, v___x_1687_);
                    v___y_1667_ = v___x_1688_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v___y_1667_ == 0 {
                    v_isSharedCheck_1677_ = (!leanh::lean_is_exclusive(v_code_1619_)) as u8;
                    if v_isSharedCheck_1677_ == 0 {
                        v_unused_1678_ = leanh::lean_ctor_get(v_code_1619_, 1);
                        leanh::lean_dec(v_unused_1678_);
                        v_unused_1679_ = leanh::lean_ctor_get(v_code_1619_, 0);
                        leanh::lean_dec(v_unused_1679_);
                        v___x_1669_ = v_code_1619_;
                        v_isShared_1670_ = v_isSharedCheck_1677_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_dec(v_code_1619_);
                        v___x_1669_ = leanh::lean_box(0);
                        v_isShared_1670_ = v_isSharedCheck_1677_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1662_);
                    leanh::lean_dec(v_a_1660_);
                    if v_isShared_1665_ == 0 {
                        leanh::lean_ctor_set(v___x_1664_, 0, v_code_1619_);
                        v___x_1681_ = v___x_1664_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1682_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_code_1619_);
                        v___x_1681_ = v_reuseFailAlloc_1682_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_1670_ == 0 {
                    leanh::lean_ctor_set(v___x_1669_, 1, v_a_1662_);
                    leanh::lean_ctor_set(v___x_1669_, 0, v_a_1660_);
                    v___x_1672_ = v___x_1669_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1676_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1660_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_a_1662_);
                    v___x_1672_ = v_reuseFailAlloc_1676_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_1665_ == 0 {
                    leanh::lean_ctor_set(v___x_1664_, 0, v___x_1672_);
                    v___x_1674_ = v___x_1664_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1675_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1672_);
                    v___x_1674_ = v_reuseFailAlloc_1675_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1674_;
            }
            11 => {
                return v___x_1681_;
            }
            12 => {
                if v_isShared_1693_ == 0 {
                    v___x_1695_ = v___x_1692_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1696_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
                    v___x_1695_ = v_reuseFailAlloc_1696_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1695_;
            }
            14 => {
                v___x_1706_ = leanh::lean_unsigned_to_nat(0);
                v___x_1707_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1(v___x_1706_, v_alts_1702_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
                if leanh::lean_obj_tag(v___x_1707_) == 0 {
                    v_a_1708_ = leanh::lean_ctor_get(v___x_1707_, 0);
                    leanh::lean_inc(v_a_1708_);
                    leanh::lean_dec_ref_known(v___x_1707_, 1);
                    if v_isShared_1705_ == 0 {
                        leanh::lean_ctor_set(v___x_1704_, 3, v_a_1708_);
                        v___x_1710_ = v___x_1704_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_1712_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_typeName_1699_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1712_, 1, v_resultType_1700_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1712_, 2, v_discr_1701_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1712_, 3, v_a_1708_);
                        v___x_1710_ = v_reuseFailAlloc_1712_;
                        state = 15;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1704_);
                    leanh::lean_dec(v_discr_1701_);
                    leanh::lean_dec_ref(v_resultType_1700_);
                    leanh::lean_dec(v_typeName_1699_);
                    v_a_1713_ = leanh::lean_ctor_get(v___x_1707_, 0);
                    v_isSharedCheck_1720_ = (!leanh::lean_is_exclusive(v___x_1707_)) as u8;
                    if v_isSharedCheck_1720_ == 0 {
                        v___x_1715_ = v___x_1707_;
                        v_isShared_1716_ = v_isSharedCheck_1720_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1713_);
                        leanh::lean_dec(v___x_1707_);
                        v___x_1715_ = leanh::lean_box(0);
                        v_isShared_1716_ = v_isSharedCheck_1720_;
                        state = 16;
                        continue;
                    }
                }
            }
            15 => {
                v___x_1711_ =
                    l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases(
                        v___x_1710_,
                        v_a_1620_,
                        v_a_1621_,
                        v_a_1622_,
                        v_a_1623_,
                    );
                return v___x_1711_;
            }
            16 => {
                if v_isShared_1716_ == 0 {
                    v___x_1718_ = v___x_1715_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1719_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
                    v___x_1718_ = v_reuseFailAlloc_1719_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1718_;
            }
            18 => {
                v___x_1731_ = lean_ptr_addr(v_k_1725_);
                v___x_1732_ = lean_ptr_addr(v_a_1727_);
                v___x_1733_ = lean_usize_dec_eq(v___x_1731_, v___x_1732_);
                if v___x_1733_ == 0 {
                    leanh::lean_inc(v_y_1724_);
                    leanh::lean_inc(v_i_1723_);
                    leanh::lean_inc(v_fvarId_1722_);
                    v_isSharedCheck_1743_ = (!leanh::lean_is_exclusive(v_code_1619_)) as u8;
                    if v_isSharedCheck_1743_ == 0 {
                        v_unused_1744_ = leanh::lean_ctor_get(v_code_1619_, 3);
                        leanh::lean_dec(v_unused_1744_);
                        v_unused_1745_ = leanh::lean_ctor_get(v_code_1619_, 2);
                        leanh::lean_dec(v_unused_1745_);
                        v_unused_1746_ = leanh::lean_ctor_get(v_code_1619_, 1);
                        leanh::lean_dec(v_unused_1746_);
                        v_unused_1747_ = leanh::lean_ctor_get(v_code_1619_, 0);
                        leanh::lean_dec(v_unused_1747_);
                        v___x_1735_ = v_code_1619_;
                        v_isShared_1736_ = v_isSharedCheck_1743_;
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_dec(v_code_1619_);
                        v___x_1735_ = leanh::lean_box(0);
                        v_isShared_1736_ = v_isSharedCheck_1743_;
                        state = 19;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1727_);
                    if v_isShared_1730_ == 0 {
                        leanh::lean_ctor_set(v___x_1729_, 0, v_code_1619_);
                        v___x_1749_ = v___x_1729_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_1750_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_code_1619_);
                        v___x_1749_ = v_reuseFailAlloc_1750_;
                        state = 22;
                        continue;
                    }
                }
            }
            19 => {
                if v_isShared_1736_ == 0 {
                    leanh::lean_ctor_set(v___x_1735_, 3, v_a_1727_);
                    v___x_1738_ = v___x_1735_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1742_ = leanh::lean_alloc_ctor(7, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_fvarId_1722_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_i_1723_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 2, v_y_1724_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 3, v_a_1727_);
                    v___x_1738_ = v_reuseFailAlloc_1742_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_1730_ == 0 {
                    leanh::lean_ctor_set(v___x_1729_, 0, v___x_1738_);
                    v___x_1740_ = v___x_1729_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1741_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1738_);
                    v___x_1740_ = v_reuseFailAlloc_1741_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1740_;
            }
            22 => {
                return v___x_1749_;
            }
            23 => {
                v___x_1761_ = lean_ptr_addr(v_k_1755_);
                v___x_1762_ = lean_ptr_addr(v_a_1757_);
                v___x_1763_ = lean_usize_dec_eq(v___x_1761_, v___x_1762_);
                if v___x_1763_ == 0 {
                    leanh::lean_inc(v_y_1754_);
                    leanh::lean_inc(v_i_1753_);
                    leanh::lean_inc(v_fvarId_1752_);
                    v_isSharedCheck_1773_ = (!leanh::lean_is_exclusive(v_code_1619_)) as u8;
                    if v_isSharedCheck_1773_ == 0 {
                        v_unused_1774_ = leanh::lean_ctor_get(v_code_1619_, 3);
                        leanh::lean_dec(v_unused_1774_);
                        v_unused_1775_ = leanh::lean_ctor_get(v_code_1619_, 2);
                        leanh::lean_dec(v_unused_1775_);
                        v_unused_1776_ = leanh::lean_ctor_get(v_code_1619_, 1);
                        leanh::lean_dec(v_unused_1776_);
                        v_unused_1777_ = leanh::lean_ctor_get(v_code_1619_, 0);
                        leanh::lean_dec(v_unused_1777_);
                        v___x_1765_ = v_code_1619_;
                        v_isShared_1766_ = v_isSharedCheck_1773_;
                        state = 24;
                        continue;
                    } else {
                        leanh::lean_dec(v_code_1619_);
                        v___x_1765_ = leanh::lean_box(0);
                        v_isShared_1766_ = v_isSharedCheck_1773_;
                        state = 24;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1757_);
                    if v_isShared_1760_ == 0 {
                        leanh::lean_ctor_set(v___x_1759_, 0, v_code_1619_);
                        v___x_1779_ = v___x_1759_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_1780_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_code_1619_);
                        v___x_1779_ = v_reuseFailAlloc_1780_;
                        state = 27;
                        continue;
                    }
                }
            }
            24 => {
                if v_isShared_1766_ == 0 {
                    leanh::lean_ctor_set(v___x_1765_, 3, v_a_1757_);
                    v___x_1768_ = v___x_1765_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_1772_ = leanh::lean_alloc_ctor(8, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_fvarId_1752_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1772_, 1, v_i_1753_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1772_, 2, v_y_1754_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1772_, 3, v_a_1757_);
                    v___x_1768_ = v_reuseFailAlloc_1772_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                if v_isShared_1760_ == 0 {
                    leanh::lean_ctor_set(v___x_1759_, 0, v___x_1768_);
                    v___x_1770_ = v___x_1759_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1771_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1768_);
                    v___x_1770_ = v_reuseFailAlloc_1771_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_1770_;
            }
            27 => {
                return v___x_1779_;
            }
            28 => {
                v___x_1793_ = lean_ptr_addr(v_k_1787_);
                v___x_1794_ = lean_ptr_addr(v_a_1789_);
                v___x_1795_ = lean_usize_dec_eq(v___x_1793_, v___x_1794_);
                if v___x_1795_ == 0 {
                    leanh::lean_inc_ref(v_ty_1786_);
                    leanh::lean_inc(v_y_1785_);
                    leanh::lean_inc(v_offset_1784_);
                    leanh::lean_inc(v_i_1783_);
                    leanh::lean_inc(v_fvarId_1782_);
                    v_isSharedCheck_1805_ = (!leanh::lean_is_exclusive(v_code_1619_)) as u8;
                    if v_isSharedCheck_1805_ == 0 {
                        v_unused_1806_ = leanh::lean_ctor_get(v_code_1619_, 5);
                        leanh::lean_dec(v_unused_1806_);
                        v_unused_1807_ = leanh::lean_ctor_get(v_code_1619_, 4);
                        leanh::lean_dec(v_unused_1807_);
                        v_unused_1808_ = leanh::lean_ctor_get(v_code_1619_, 3);
                        leanh::lean_dec(v_unused_1808_);
                        v_unused_1809_ = leanh::lean_ctor_get(v_code_1619_, 2);
                        leanh::lean_dec(v_unused_1809_);
                        v_unused_1810_ = leanh::lean_ctor_get(v_code_1619_, 1);
                        leanh::lean_dec(v_unused_1810_);
                        v_unused_1811_ = leanh::lean_ctor_get(v_code_1619_, 0);
                        leanh::lean_dec(v_unused_1811_);
                        v___x_1797_ = v_code_1619_;
                        v_isShared_1798_ = v_isSharedCheck_1805_;
                        state = 29;
                        continue;
                    } else {
                        leanh::lean_dec(v_code_1619_);
                        v___x_1797_ = leanh::lean_box(0);
                        v_isShared_1798_ = v_isSharedCheck_1805_;
                        state = 29;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1789_);
                    if v_isShared_1792_ == 0 {
                        leanh::lean_ctor_set(v___x_1791_, 0, v_code_1619_);
                        v___x_1813_ = v___x_1791_;
                        state = 32;
                        continue;
                    } else {
                        v_reuseFailAlloc_1814_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_code_1619_);
                        v___x_1813_ = v_reuseFailAlloc_1814_;
                        state = 32;
                        continue;
                    }
                }
            }
            29 => {
                if v_isShared_1798_ == 0 {
                    leanh::lean_ctor_set(v___x_1797_, 5, v_a_1789_);
                    v___x_1800_ = v___x_1797_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1804_ = leanh::lean_alloc_ctor(9, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_fvarId_1782_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1804_, 1, v_i_1783_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1804_, 2, v_offset_1784_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1804_, 3, v_y_1785_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1804_, 4, v_ty_1786_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1804_, 5, v_a_1789_);
                    v___x_1800_ = v_reuseFailAlloc_1804_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                if v_isShared_1792_ == 0 {
                    leanh::lean_ctor_set(v___x_1791_, 0, v___x_1800_);
                    v___x_1802_ = v___x_1791_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_1803_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1800_);
                    v___x_1802_ = v_reuseFailAlloc_1803_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_1802_;
            }
            32 => {
                return v___x_1813_;
            }
            33 => {
                v___x_1824_ = lean_ptr_addr(v_k_1818_);
                v___x_1825_ = lean_ptr_addr(v_a_1820_);
                v___x_1826_ = lean_usize_dec_eq(v___x_1824_, v___x_1825_);
                if v___x_1826_ == 0 {
                    leanh::lean_inc(v_cidx_1817_);
                    leanh::lean_inc(v_fvarId_1816_);
                    v_isSharedCheck_1836_ = (!leanh::lean_is_exclusive(v_code_1619_)) as u8;
                    if v_isSharedCheck_1836_ == 0 {
                        v_unused_1837_ = leanh::lean_ctor_get(v_code_1619_, 2);
                        leanh::lean_dec(v_unused_1837_);
                        v_unused_1838_ = leanh::lean_ctor_get(v_code_1619_, 1);
                        leanh::lean_dec(v_unused_1838_);
                        v_unused_1839_ = leanh::lean_ctor_get(v_code_1619_, 0);
                        leanh::lean_dec(v_unused_1839_);
                        v___x_1828_ = v_code_1619_;
                        v_isShared_1829_ = v_isSharedCheck_1836_;
                        state = 34;
                        continue;
                    } else {
                        leanh::lean_dec(v_code_1619_);
                        v___x_1828_ = leanh::lean_box(0);
                        v_isShared_1829_ = v_isSharedCheck_1836_;
                        state = 34;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1820_);
                    if v_isShared_1823_ == 0 {
                        leanh::lean_ctor_set(v___x_1822_, 0, v_code_1619_);
                        v___x_1841_ = v___x_1822_;
                        state = 37;
                        continue;
                    } else {
                        v_reuseFailAlloc_1842_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_code_1619_);
                        v___x_1841_ = v_reuseFailAlloc_1842_;
                        state = 37;
                        continue;
                    }
                }
            }
            34 => {
                if v_isShared_1829_ == 0 {
                    leanh::lean_ctor_set(v___x_1828_, 2, v_a_1820_);
                    v___x_1831_ = v___x_1828_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_1835_ = leanh::lean_alloc_ctor(10, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_fvarId_1816_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1835_, 1, v_cidx_1817_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1835_, 2, v_a_1820_);
                    v___x_1831_ = v_reuseFailAlloc_1835_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_1823_ == 0 {
                    leanh::lean_ctor_set(v___x_1822_, 0, v___x_1831_);
                    v___x_1833_ = v___x_1822_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1834_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1831_);
                    v___x_1833_ = v_reuseFailAlloc_1834_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_1833_;
            }
            37 => {
                return v___x_1841_;
            }
            38 => {
                v___x_1854_ = lean_ptr_addr(v_k_1848_);
                v___x_1855_ = lean_ptr_addr(v_a_1850_);
                v___x_1856_ = lean_usize_dec_eq(v___x_1854_, v___x_1855_);
                if v___x_1856_ == 0 {
                    leanh::lean_inc(v_n_1845_);
                    leanh::lean_inc(v_fvarId_1844_);
                    v_isSharedCheck_1866_ = (!leanh::lean_is_exclusive(v_code_1619_)) as u8;
                    if v_isSharedCheck_1866_ == 0 {
                        v_unused_1867_ = leanh::lean_ctor_get(v_code_1619_, 2);
                        leanh::lean_dec(v_unused_1867_);
                        v_unused_1868_ = leanh::lean_ctor_get(v_code_1619_, 1);
                        leanh::lean_dec(v_unused_1868_);
                        v_unused_1869_ = leanh::lean_ctor_get(v_code_1619_, 0);
                        leanh::lean_dec(v_unused_1869_);
                        v___x_1858_ = v_code_1619_;
                        v_isShared_1859_ = v_isSharedCheck_1866_;
                        state = 39;
                        continue;
                    } else {
                        leanh::lean_dec(v_code_1619_);
                        v___x_1858_ = leanh::lean_box(0);
                        v_isShared_1859_ = v_isSharedCheck_1866_;
                        state = 39;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1850_);
                    if v_isShared_1853_ == 0 {
                        leanh::lean_ctor_set(v___x_1852_, 0, v_code_1619_);
                        v___x_1871_ = v___x_1852_;
                        state = 42;
                        continue;
                    } else {
                        v_reuseFailAlloc_1872_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_code_1619_);
                        v___x_1871_ = v_reuseFailAlloc_1872_;
                        state = 42;
                        continue;
                    }
                }
            }
            39 => {
                if v_isShared_1859_ == 0 {
                    leanh::lean_ctor_set(v___x_1858_, 2, v_a_1850_);
                    v___x_1861_ = v___x_1858_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_1865_ = leanh::lean_alloc_ctor(11, 3, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_fvarId_1844_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1865_, 1, v_n_1845_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1865_, 2, v_a_1850_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1865_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_check_1846_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1865_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                        v_persistent_1847_,
                    );
                    v___x_1861_ = v_reuseFailAlloc_1865_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_1853_ == 0 {
                    leanh::lean_ctor_set(v___x_1852_, 0, v___x_1861_);
                    v___x_1863_ = v___x_1852_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1864_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1861_);
                    v___x_1863_ = v_reuseFailAlloc_1864_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_1863_;
            }
            42 => {
                return v___x_1871_;
            }
            43 => {
                v___x_1885_ = lean_ptr_addr(v_k_1879_);
                v___x_1886_ = lean_ptr_addr(v_a_1881_);
                v___x_1887_ = lean_usize_dec_eq(v___x_1885_, v___x_1886_);
                if v___x_1887_ == 0 {
                    leanh::lean_inc(v_objs_x3f_1878_);
                    leanh::lean_inc(v_n_1875_);
                    leanh::lean_inc(v_fvarId_1874_);
                    v_isSharedCheck_1897_ = (!leanh::lean_is_exclusive(v_code_1619_)) as u8;
                    if v_isSharedCheck_1897_ == 0 {
                        v_unused_1898_ = leanh::lean_ctor_get(v_code_1619_, 3);
                        leanh::lean_dec(v_unused_1898_);
                        v_unused_1899_ = leanh::lean_ctor_get(v_code_1619_, 2);
                        leanh::lean_dec(v_unused_1899_);
                        v_unused_1900_ = leanh::lean_ctor_get(v_code_1619_, 1);
                        leanh::lean_dec(v_unused_1900_);
                        v_unused_1901_ = leanh::lean_ctor_get(v_code_1619_, 0);
                        leanh::lean_dec(v_unused_1901_);
                        v___x_1889_ = v_code_1619_;
                        v_isShared_1890_ = v_isSharedCheck_1897_;
                        state = 44;
                        continue;
                    } else {
                        leanh::lean_dec(v_code_1619_);
                        v___x_1889_ = leanh::lean_box(0);
                        v_isShared_1890_ = v_isSharedCheck_1897_;
                        state = 44;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1881_);
                    if v_isShared_1884_ == 0 {
                        leanh::lean_ctor_set(v___x_1883_, 0, v_code_1619_);
                        v___x_1903_ = v___x_1883_;
                        state = 47;
                        continue;
                    } else {
                        v_reuseFailAlloc_1904_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_code_1619_);
                        v___x_1903_ = v_reuseFailAlloc_1904_;
                        state = 47;
                        continue;
                    }
                }
            }
            44 => {
                if v_isShared_1890_ == 0 {
                    leanh::lean_ctor_set(v___x_1889_, 3, v_a_1881_);
                    v___x_1892_ = v___x_1889_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_1896_ = leanh::lean_alloc_ctor(12, 4, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_fvarId_1874_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_n_1875_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 2, v_objs_x3f_1878_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 3, v_a_1881_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1896_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        v_check_1876_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1896_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
                        v_persistent_1877_,
                    );
                    v___x_1892_ = v_reuseFailAlloc_1896_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_1884_ == 0 {
                    leanh::lean_ctor_set(v___x_1883_, 0, v___x_1892_);
                    v___x_1894_ = v___x_1883_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_1895_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1892_);
                    v___x_1894_ = v_reuseFailAlloc_1895_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_1894_;
            }
            47 => {
                return v___x_1903_;
            }
            48 => {
                v___x_1913_ = lean_ptr_addr(v_k_1907_);
                v___x_1914_ = lean_ptr_addr(v_a_1909_);
                v___x_1915_ = lean_usize_dec_eq(v___x_1913_, v___x_1914_);
                if v___x_1915_ == 0 {
                    leanh::lean_inc(v_fvarId_1906_);
                    v_isSharedCheck_1925_ = (!leanh::lean_is_exclusive(v_code_1619_)) as u8;
                    if v_isSharedCheck_1925_ == 0 {
                        v_unused_1926_ = leanh::lean_ctor_get(v_code_1619_, 1);
                        leanh::lean_dec(v_unused_1926_);
                        v_unused_1927_ = leanh::lean_ctor_get(v_code_1619_, 0);
                        leanh::lean_dec(v_unused_1927_);
                        v___x_1917_ = v_code_1619_;
                        v_isShared_1918_ = v_isSharedCheck_1925_;
                        state = 49;
                        continue;
                    } else {
                        leanh::lean_dec(v_code_1619_);
                        v___x_1917_ = leanh::lean_box(0);
                        v_isShared_1918_ = v_isSharedCheck_1925_;
                        state = 49;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1909_);
                    if v_isShared_1912_ == 0 {
                        leanh::lean_ctor_set(v___x_1911_, 0, v_code_1619_);
                        v___x_1929_ = v___x_1911_;
                        state = 52;
                        continue;
                    } else {
                        v_reuseFailAlloc_1930_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_code_1619_);
                        v___x_1929_ = v_reuseFailAlloc_1930_;
                        state = 52;
                        continue;
                    }
                }
            }
            49 => {
                if v_isShared_1918_ == 0 {
                    leanh::lean_ctor_set(v___x_1917_, 1, v_a_1909_);
                    v___x_1920_ = v___x_1917_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_1924_ = leanh::lean_alloc_ctor(13, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_fvarId_1906_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_a_1909_);
                    v___x_1920_ = v_reuseFailAlloc_1924_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                if v_isShared_1912_ == 0 {
                    leanh::lean_ctor_set(v___x_1911_, 0, v___x_1920_);
                    v___x_1922_ = v___x_1911_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_1923_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1920_);
                    v___x_1922_ = v_reuseFailAlloc_1923_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                return v___x_1922_;
            }
            52 => {
                return v___x_1929_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase___boxed(
    mut v_code_1933_: *mut leanh::LeanObject,
    mut v_a_1934_: *mut leanh::LeanObject,
    mut v_a_1935_: *mut leanh::LeanObject,
    mut v_a_1936_: *mut leanh::LeanObject,
    mut v_a_1937_: *mut leanh::LeanObject,
    mut v_a_1938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1939_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(
        v_code_1933_,
        v_a_1934_,
        v_a_1935_,
        v_a_1936_,
        v_a_1937_,
    );
    leanh::lean_dec(v_a_1937_);
    leanh::lean_dec_ref(v_a_1936_);
    leanh::lean_dec(v_a_1935_);
    leanh::lean_dec_ref(v_a_1934_);
    return v_res_1939_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1(
    mut v_i_1940_: *mut leanh::LeanObject,
    mut v_as_1941_: *mut leanh::LeanObject,
    mut v___y_1942_: *mut leanh::LeanObject,
    mut v___y_1943_: *mut leanh::LeanObject,
    mut v___y_1944_: *mut leanh::LeanObject,
    mut v___y_1945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: u8 = 0;
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: usize = 0;
    let mut v___x_1955_: usize = 0;
    let mut v___x_1956_: u8 = 0;
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1967_: u8 = 0;
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1971_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1947_ = lean_array_get_size(v_as_1941_);
                v___x_1948_ = lean_nat_dec_lt(v_i_1940_, v___x_1947_);
                if v___x_1948_ == 0 {
                    leanh::lean_dec(v_i_1940_);
                    v___x_1949_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1949_, 0, v_as_1941_);
                    return v___x_1949_;
                } else {
                    v___f_1950_ = leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase___boxed as *mut core::ffi::c_void, 6, 0);
                    v_a_1951_ = lean_array_fget_borrowed(v_as_1941_, v_i_1940_);
                    leanh::lean_inc(v_a_1951_);
                    v___x_1952_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg(v_a_1951_, v___f_1950_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
                    if leanh::lean_obj_tag(v___x_1952_) == 0 {
                        v_a_1953_ = leanh::lean_ctor_get(v___x_1952_, 0);
                        leanh::lean_inc(v_a_1953_);
                        leanh::lean_dec_ref_known(v___x_1952_, 1);
                        v___x_1954_ = lean_ptr_addr(v_a_1951_);
                        v___x_1955_ = lean_ptr_addr(v_a_1953_);
                        v___x_1956_ = lean_usize_dec_eq(v___x_1954_, v___x_1955_);
                        if v___x_1956_ == 0 {
                            v___x_1957_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1958_ = lean_nat_add(v_i_1940_, v___x_1957_);
                            v___x_1959_ = lean_array_fset(v_as_1941_, v_i_1940_, v_a_1953_);
                            leanh::lean_dec(v_i_1940_);
                            v_i_1940_ = v___x_1958_;
                            v_as_1941_ = v___x_1959_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_1953_);
                            v___x_1961_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1962_ = lean_nat_add(v_i_1940_, v___x_1961_);
                            leanh::lean_dec(v_i_1940_);
                            v_i_1940_ = v___x_1962_;
                            state = 0;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_as_1941_);
                        leanh::lean_dec(v_i_1940_);
                        v_a_1964_ = leanh::lean_ctor_get(v___x_1952_, 0);
                        v_isSharedCheck_1971_ =
                            (!leanh::lean_is_exclusive(v___x_1952_)) as u8;
                        if v_isSharedCheck_1971_ == 0 {
                            v___x_1966_ = v___x_1952_;
                            v_isShared_1967_ = v_isSharedCheck_1971_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1964_);
                            leanh::lean_dec(v___x_1952_);
                            v___x_1966_ = leanh::lean_box(0);
                            v_isShared_1967_ = v_isSharedCheck_1971_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1967_ == 0 {
                    v___x_1969_ = v___x_1966_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1970_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
                    v___x_1969_ = v_reuseFailAlloc_1970_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1969_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1___boxed(
    mut v_i_1972_: *mut leanh::LeanObject,
    mut v_as_1973_: *mut leanh::LeanObject,
    mut v___y_1974_: *mut leanh::LeanObject,
    mut v___y_1975_: *mut leanh::LeanObject,
    mut v___y_1976_: *mut leanh::LeanObject,
    mut v___y_1977_: *mut leanh::LeanObject,
    mut v___y_1978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1979_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1(v_i_1972_, v_as_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
    leanh::lean_dec(v___y_1977_);
    leanh::lean_dec_ref(v___y_1976_);
    leanh::lean_dec(v___y_1975_);
    leanh::lean_dec_ref(v___y_1974_);
    return v_res_1979_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg(
    mut v_f_1980_: *mut leanh::LeanObject,
    mut v_v_1981_: *mut leanh::LeanObject,
    mut v___y_1982_: *mut leanh::LeanObject,
    mut v___y_1983_: *mut leanh::LeanObject,
    mut v___y_1984_: *mut leanh::LeanObject,
    mut v___y_1985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_code_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1990_: u8 = 0;
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1995_: u8 = 0;
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2002_: u8 = 0;
    let mut v_a_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2006_: u8 = 0;
    let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2010_: u8 = 0;
    let mut v_isSharedCheck_2011_: u8 = 0;
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_v_1981_) == 0 {
                    v_code_1987_ = leanh::lean_ctor_get(v_v_1981_, 0);
                    v_isSharedCheck_2011_ = (!leanh::lean_is_exclusive(v_v_1981_)) as u8;
                    if v_isSharedCheck_2011_ == 0 {
                        v___x_1989_ = v_v_1981_;
                        v_isShared_1990_ = v_isSharedCheck_2011_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_code_1987_);
                        leanh::lean_dec(v_v_1981_);
                        v___x_1989_ = leanh::lean_box(0);
                        v_isShared_1990_ = v_isSharedCheck_2011_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_f_1980_);
                    v___x_2012_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2012_, 0, v_v_1981_);
                    return v___x_2012_;
                }
            }
            1 => {
                leanh::lean_inc(v___y_1985_);
                leanh::lean_inc_ref(v___y_1984_);
                leanh::lean_inc(v___y_1983_);
                leanh::lean_inc_ref(v___y_1982_);
                v___x_1991_ = leanh::lean_apply_6(
                    v_f_1980_,
                    v_code_1987_,
                    v___y_1982_,
                    v___y_1983_,
                    v___y_1984_,
                    v___y_1985_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1991_) == 0 {
                    v_a_1992_ = leanh::lean_ctor_get(v___x_1991_, 0);
                    v_isSharedCheck_2002_ = (!leanh::lean_is_exclusive(v___x_1991_)) as u8;
                    if v_isSharedCheck_2002_ == 0 {
                        v___x_1994_ = v___x_1991_;
                        v_isShared_1995_ = v_isSharedCheck_2002_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1992_);
                        leanh::lean_dec(v___x_1991_);
                        v___x_1994_ = leanh::lean_box(0);
                        v_isShared_1995_ = v_isSharedCheck_2002_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1989_);
                    v_a_2003_ = leanh::lean_ctor_get(v___x_1991_, 0);
                    v_isSharedCheck_2010_ = (!leanh::lean_is_exclusive(v___x_1991_)) as u8;
                    if v_isSharedCheck_2010_ == 0 {
                        v___x_2005_ = v___x_1991_;
                        v_isShared_2006_ = v_isSharedCheck_2010_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2003_);
                        leanh::lean_dec(v___x_1991_);
                        v___x_2005_ = leanh::lean_box(0);
                        v_isShared_2006_ = v_isSharedCheck_2010_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1990_ == 0 {
                    leanh::lean_ctor_set(v___x_1989_, 0, v_a_1992_);
                    v___x_1997_ = v___x_1989_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2001_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1992_);
                    v___x_1997_ = v_reuseFailAlloc_2001_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1995_ == 0 {
                    leanh::lean_ctor_set(v___x_1994_, 0, v___x_1997_);
                    v___x_1999_ = v___x_1994_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2000_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1997_);
                    v___x_1999_ = v_reuseFailAlloc_2000_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1999_;
            }
            5 => {
                if v_isShared_2006_ == 0 {
                    v___x_2008_ = v___x_2005_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2009_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2003_);
                    v___x_2008_ = v_reuseFailAlloc_2009_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2008_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg___boxed(
    mut v_f_2013_: *mut leanh::LeanObject,
    mut v_v_2014_: *mut leanh::LeanObject,
    mut v___y_2015_: *mut leanh::LeanObject,
    mut v___y_2016_: *mut leanh::LeanObject,
    mut v___y_2017_: *mut leanh::LeanObject,
    mut v___y_2018_: *mut leanh::LeanObject,
    mut v___y_2019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2020_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg(v_f_2013_, v_v_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
    leanh::lean_dec(v___y_2018_);
    leanh::lean_dec_ref(v___y_2017_);
    leanh::lean_dec(v___y_2016_);
    leanh::lean_dec_ref(v___y_2015_);
    return v_res_2020_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0(
    mut v_pu_2021_: u8,
    mut v_f_2022_: *mut leanh::LeanObject,
    mut v_v_2023_: *mut leanh::LeanObject,
    mut v___y_2024_: *mut leanh::LeanObject,
    mut v___y_2025_: *mut leanh::LeanObject,
    mut v___y_2026_: *mut leanh::LeanObject,
    mut v___y_2027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2029_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg(v_f_2022_, v_v_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
    return v___x_2029_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___boxed(
    mut v_pu_2030_: *mut leanh::LeanObject,
    mut v_f_2031_: *mut leanh::LeanObject,
    mut v_v_2032_: *mut leanh::LeanObject,
    mut v___y_2033_: *mut leanh::LeanObject,
    mut v___y_2034_: *mut leanh::LeanObject,
    mut v___y_2035_: *mut leanh::LeanObject,
    mut v___y_2036_: *mut leanh::LeanObject,
    mut v___y_2037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_2038_: u8 = 0;
    let mut v_res_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_2038_ = (leanh::lean_unbox(v_pu_2030_) as u8);
    v_res_2039_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0(v_pu_boxed_2038_, v_f_2031_, v_v_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
    leanh::lean_dec(v___y_2036_);
    leanh::lean_dec_ref(v___y_2035_);
    leanh::lean_dec(v___y_2034_);
    leanh::lean_dec_ref(v___y_2033_);
    return v_res_2039_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase(
    mut v_decl_2041_: *mut leanh::LeanObject,
    mut v_a_2042_: *mut leanh::LeanObject,
    mut v_a_2043_: *mut leanh::LeanObject,
    mut v_a_2044_: *mut leanh::LeanObject,
    mut v_a_2045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toSignature_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursive_2049_: u8 = 0;
    let mut v_inlineAttr_x3f_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2053_: u8 = 0;
    let mut v___f_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2059_: u8 = 0;
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2066_: u8 = 0;
    let mut v_a_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2070_: u8 = 0;
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2074_: u8 = 0;
    let mut v_isSharedCheck_2075_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSignature_2047_ = leanh::lean_ctor_get(v_decl_2041_, 0);
                v_value_2048_ = leanh::lean_ctor_get(v_decl_2041_, 1);
                v_recursive_2049_ = leanh::lean_ctor_get_uint8(
                    v_decl_2041_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_inlineAttr_x3f_2050_ = leanh::lean_ctor_get(v_decl_2041_, 2);
                v_isSharedCheck_2075_ = (!leanh::lean_is_exclusive(v_decl_2041_)) as u8;
                if v_isSharedCheck_2075_ == 0 {
                    v___x_2052_ = v_decl_2041_;
                    v_isShared_2053_ = v_isSharedCheck_2075_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_inlineAttr_x3f_2050_);
                    leanh::lean_inc(v_value_2048_);
                    leanh::lean_inc(v_toSignature_2047_);
                    leanh::lean_dec(v_decl_2041_);
                    v___x_2052_ = leanh::lean_box(0);
                    v_isShared_2053_ = v_isSharedCheck_2075_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_2054_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___closed__0;
                v___x_2055_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg(v___f_2054_, v_value_2048_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
                if leanh::lean_obj_tag(v___x_2055_) == 0 {
                    v_a_2056_ = leanh::lean_ctor_get(v___x_2055_, 0);
                    v_isSharedCheck_2066_ = (!leanh::lean_is_exclusive(v___x_2055_)) as u8;
                    if v_isSharedCheck_2066_ == 0 {
                        v___x_2058_ = v___x_2055_;
                        v_isShared_2059_ = v_isSharedCheck_2066_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2056_);
                        leanh::lean_dec(v___x_2055_);
                        v___x_2058_ = leanh::lean_box(0);
                        v_isShared_2059_ = v_isSharedCheck_2066_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2052_);
                    leanh::lean_dec(v_inlineAttr_x3f_2050_);
                    leanh::lean_dec_ref(v_toSignature_2047_);
                    v_a_2067_ = leanh::lean_ctor_get(v___x_2055_, 0);
                    v_isSharedCheck_2074_ = (!leanh::lean_is_exclusive(v___x_2055_)) as u8;
                    if v_isSharedCheck_2074_ == 0 {
                        v___x_2069_ = v___x_2055_;
                        v_isShared_2070_ = v_isSharedCheck_2074_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2067_);
                        leanh::lean_dec(v___x_2055_);
                        v___x_2069_ = leanh::lean_box(0);
                        v_isShared_2070_ = v_isSharedCheck_2074_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2053_ == 0 {
                    leanh::lean_ctor_set(v___x_2052_, 1, v_a_2056_);
                    v___x_2061_ = v___x_2052_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2065_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_toSignature_2047_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2065_, 1, v_a_2056_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2065_, 2, v_inlineAttr_x3f_2050_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2065_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_recursive_2049_,
                    );
                    v___x_2061_ = v_reuseFailAlloc_2065_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2059_ == 0 {
                    leanh::lean_ctor_set(v___x_2058_, 0, v___x_2061_);
                    v___x_2063_ = v___x_2058_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2064_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2061_);
                    v___x_2063_ = v_reuseFailAlloc_2064_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2063_;
            }
            5 => {
                if v_isShared_2070_ == 0 {
                    v___x_2072_ = v___x_2069_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2073_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
                    v___x_2072_ = v_reuseFailAlloc_2073_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2072_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___boxed(
    mut v_decl_2076_: *mut leanh::LeanObject,
    mut v_a_2077_: *mut leanh::LeanObject,
    mut v_a_2078_: *mut leanh::LeanObject,
    mut v_a_2079_: *mut leanh::LeanObject,
    mut v_a_2080_: *mut leanh::LeanObject,
    mut v_a_2081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2082_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase(
        v_decl_2076_,
        v_a_2077_,
        v_a_2078_,
        v_a_2079_,
        v_a_2080_,
    );
    leanh::lean_dec(v_a_2080_);
    leanh::lean_dec_ref(v_a_2079_);
    leanh::lean_dec(v_a_2078_);
    leanh::lean_dec_ref(v_a_2077_);
    return v_res_2082_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0(
    mut v_as_2083_: *mut leanh::LeanObject,
    mut v_i_2084_: usize,
    mut v_stop_2085_: usize,
) -> u8 {
    let mut v___x_2086_: u8 = 0;
    let mut v___x_2087_: u8 = 0;
    let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: usize = 0;
    let mut v___x_2090_: usize = 0;
    let mut v___x_2092_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2086_ = lean_usize_dec_eq(v_i_2084_, v_stop_2085_);
                if v___x_2086_ == 0 {
                    v___x_2087_ = 1;
                    v___x_2088_ = lean_array_uget_borrowed(v_as_2083_, v_i_2084_);
                    if leanh::lean_obj_tag(v___x_2088_) == 2 {
                        return v___x_2087_;
                    } else {
                        if v___x_2086_ == 0 {
                            v___x_2089_ = 1usize;
                            v___x_2090_ = lean_usize_add(v_i_2084_, v___x_2089_);
                            v_i_2084_ = v___x_2090_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_2087_;
                        }
                    }
                } else {
                    v___x_2092_ = 0;
                    return v___x_2092_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0___boxed(
    mut v_as_2093_: *mut leanh::LeanObject,
    mut v_i_2094_: *mut leanh::LeanObject,
    mut v_stop_2095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2096_: usize = 0;
    let mut v_stop_boxed_2097_: usize = 0;
    let mut v_res_2098_: u8 = 0;
    let mut v_r_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2096_ = leanh::lean_unbox_usize(v_i_2094_);
    leanh::lean_dec(v_i_2094_);
    v_stop_boxed_2097_ = leanh::lean_unbox_usize(v_stop_2095_);
    leanh::lean_dec(v_stop_2095_);
    v_res_2098_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0(v_as_2093_, v_i_boxed_2096_, v_stop_boxed_2097_);
    leanh::lean_dec_ref(v_as_2093_);
    v_r_2099_ = leanh::lean_box((v_res_2098_) as usize);
    return v_r_2099_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ensureHasDefault(
    mut v_alts_2100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: u8 = 0;
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_last_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: u8 = 0;
    let mut v___x_2120_: usize = 0;
    let mut v___x_2121_: usize = 0;
    let mut v___x_2122_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2106_ = leanh::lean_unsigned_to_nat(0);
                v___x_2107_ = lean_array_get_size(v_alts_2100_);
                v___x_2119_ = lean_nat_dec_lt(v___x_2106_, v___x_2107_);
                if v___x_2119_ == 0 {
                    state = 2;
                    continue;
                } else {
                    if v___x_2119_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        v___x_2120_ = 0usize;
                        v___x_2121_ = lean_usize_of_nat(v___x_2107_);
                        v___x_2122_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0(v_alts_2100_, v___x_2120_, v___x_2121_);
                        if v___x_2122_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            return v_alts_2100_;
                        }
                    }
                }
            }
            1 => {
                v___x_2104_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2104_, 0, v___y_2103_);
                v___x_2105_ = lean_array_push(v___y_2102_, v___x_2104_);
                return v___x_2105_;
            }
            2 => {
                v___x_2109_ = leanh::lean_unsigned_to_nat(2);
                v___x_2110_ = lean_nat_dec_lt(v___x_2107_, v___x_2109_);
                if v___x_2110_ == 0 {
                    v___x_2111_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0_once), _init_l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0);
                    v___x_2112_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2113_ = lean_nat_sub(v___x_2107_, v___x_2112_);
                    v_last_2114_ = lean_array_get(v___x_2111_, v_alts_2100_, v___x_2113_);
                    leanh::lean_dec(v___x_2113_);
                    v_alts_2115_ = lean_array_pop(v_alts_2100_);
                    match leanh::lean_obj_tag(v_last_2114_) {
                        0 => {
                            v_code_2116_ = leanh::lean_ctor_get(v_last_2114_, 2);
                            leanh::lean_inc_ref(v_code_2116_);
                            leanh::lean_dec_ref_known(v_last_2114_, 3);
                            v___y_2102_ = v_alts_2115_;
                            v___y_2103_ = v_code_2116_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_2117_ = leanh::lean_ctor_get(v_last_2114_, 1);
                            leanh::lean_inc_ref(v_code_2117_);
                            leanh::lean_dec_ref_known(v_last_2114_, 2);
                            v___y_2102_ = v_alts_2115_;
                            v___y_2103_ = v_code_2117_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_2118_ = leanh::lean_ctor_get(v_last_2114_, 0);
                            leanh::lean_inc_ref(v_code_2118_);
                            leanh::lean_dec_ref_known(v_last_2114_, 1);
                            v___y_2102_ = v_alts_2115_;
                            v___y_2103_ = v_code_2118_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_alts_2100_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_simpCase___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: u8 = 0;
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2127_ = leanh::lean_unsigned_to_nat(0);
    v___x_2128_ = l_Lean_Compiler_LCNF_simpCase___closed__2;
    v___x_2129_ = 2;
    v___x_2130_ = l_Lean_Compiler_LCNF_simpCase___closed__1;
    v___x_2131_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(
        v___x_2130_,
        v___x_2129_,
        v___x_2128_,
        v___x_2127_,
    );
    return v___x_2131_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_simpCase() -> *mut leanh::LeanObject {
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2132_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_simpCase___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_simpCase___closed__3_once),
        _init_l_Lean_Compiler_LCNF_simpCase___closed__3,
    );
    return v___x_2132_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: u8 = 0;
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2203_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_;
    v___x_2204_ = 1;
    v___x_2205_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_;
    v___x_2206_ = l_Lean_registerTraceClass(v___x_2203_, v___x_2204_, v___x_2205_);
    return v___x_2206_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2____boxed(
    mut v_a_2207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2208_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_();
    return v_res_2208_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_SimpCase(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_AlphaEqv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Compiler_LCNF_simpCase = _init_l_Lean_Compiler_LCNF_simpCase();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_simpCase);
    res = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_SimpCase(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_SimpCase(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_AlphaEqv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_SimpCase(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_SimpCase(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_SimpCase(builtin);
}
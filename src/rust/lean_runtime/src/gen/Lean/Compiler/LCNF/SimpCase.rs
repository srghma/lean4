// Lean compiler output
// Module: Lean.Compiler.LCNF.SimpCase
// Imports: Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.PassManager Lean.Compiler.LCNF.AlphaEqv Init.Omega
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_num___override, l_Lean_Name_str___override,
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_pop, lean_array_size, lean_array_uget_borrowed,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_5,
    lean_apply_6, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__1_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__0_value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83, 105, 109, 112, 67, 97, 115, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__1_value: LeanStringObject<72> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 72, m_capacity: 72, m_length: 71, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83, 105, 109, 112, 67, 97, 115, 101, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 97, 100, 100, 68, 101, 102, 97, 117, 108, 116, 65, 108, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__2_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__2_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__0_value) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_simpCase___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_simpCase___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_simpCase___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_simpCase___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_simpCase___closed__0_value) as *mut LeanObject,
        152573878402112580 as *mut LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_simpCase___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_simpCase___closed__1_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_simpCase___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___boxed
            as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_simpCase___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_simpCase___closed__2_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_simpCase___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_simpCase___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_simpCase: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,2042452093243897853 as *mut LeanObject] };
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_simpCase___closed__0_value) as *mut LeanObject,12233630713565377370 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,1501781890156459336 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,4203849195465939425 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [83, 105, 109, 112, 67, 97, 115, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,15170478620010304916 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,17494640641286690197 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,17944010275935732608 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,14737011660976769498 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,283130039692640827 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,7247137155347499786 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,1783459115286046307 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,15595711010524809390 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,5029508184210329612 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,16421428518153402829 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,7808061475727609480 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,((( 1808010913 as usize) << 1) | 1) as *mut LeanObject,13938647319545547308 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,4295743257037208291 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,1121150272219189379 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,11641711822422586182 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg(
    mut v_upperBound_1105_: *mut LeanObject,
    mut v_alts_1106_: *mut LeanObject,
    mut v_code_1107_: *mut LeanObject,
    mut v_a_1108_: *mut LeanObject,
    mut v_b_1109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1110_: u8 = 0;
    let mut v___x_1111_: u8 = 0;
    let mut v_n_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: u8 = 0;
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1110_ = lean_nat_dec_lt(v_a_1108_, v_upperBound_1105_);
                if v___x_1110_ == 0 {
                    lean_dec(v_a_1108_);
                    lean_dec_ref(v_code_1107_);
                    return v_b_1109_;
                } else {
                    v___x_1111_ = 1;
                    v_n_1112_ = lean_unsigned_to_nat(1);
                    v___x_1121_ = lean_array_fget_borrowed(v_alts_1106_, v_a_1108_);
                    match lean_obj_tag(v___x_1121_) {
                        0 => {
                            v_code_1122_ = lean_ctor_get(v___x_1121_, 2);
                            lean_inc_ref(v_code_1122_);
                            v___y_1118_ = v_code_1122_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_code_1123_ = lean_ctor_get(v___x_1121_, 1);
                            lean_inc_ref(v_code_1123_);
                            v___y_1118_ = v_code_1123_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            v_code_1124_ = lean_ctor_get(v___x_1121_, 0);
                            lean_inc_ref(v_code_1124_);
                            v___y_1118_ = v_code_1124_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1115_ = lean_nat_add(v_a_1108_, v_n_1112_);
                lean_dec(v_a_1108_);
                v_a_1108_ = v___x_1115_;
                v_b_1109_ = v_a_1114_;
                state = 0;
                continue;
            }
            2 => {
                lean_inc_ref(v_code_1107_);
                v___x_1119_ =
                    l_Lean_Compiler_LCNF_Code_alphaEqv(v___x_1111_, v___y_1118_, v_code_1107_);
                if v___x_1119_ == 0 {
                    v_a_1114_ = v_b_1109_;
                    state = 1;
                    continue;
                } else {
                    v___x_1120_ = lean_nat_add(v_b_1109_, v_n_1112_);
                    lean_dec(v_b_1109_);
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
    mut v_upperBound_1125_: *mut LeanObject,
    mut v_alts_1126_: *mut LeanObject,
    mut v_code_1127_: *mut LeanObject,
    mut v_a_1128_: *mut LeanObject,
    mut v_b_1129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1130_: *mut LeanObject = core::ptr::null_mut();
    v_res_1130_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg(v_upperBound_1125_, v_alts_1126_, v_code_1127_, v_a_1128_, v_b_1129_);
    lean_dec_ref(v_alts_1126_);
    lean_dec(v_upperBound_1125_);
    return v_res_1130_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0()
-> *mut LeanObject {
    let mut v___x_1131_: u8 = 0;
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    v___x_1131_ = 1;
    v___x_1132_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(v___x_1131_);
    return v___x_1132_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf(
    mut v_alts_1133_: *mut LeanObject,
    mut v_i_1134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    v___x_1135_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0_once), _init_l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0);
    v_n_1136_ = lean_unsigned_to_nat(1);
    v___x_1137_ = lean_nat_add(v_i_1134_, v_n_1136_);
    v___x_1138_ = lean_array_get_size(v_alts_1133_);
    v___x_1139_ = lean_array_get_borrowed(v___x_1135_, v_alts_1133_, v_i_1134_);
    match lean_obj_tag(v___x_1139_) {
        0 => {
            let mut v_code_1140_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
            v_code_1140_ = lean_ctor_get(v___x_1139_, 2);
            lean_inc_ref(v_code_1140_);
            v___x_1141_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg(v___x_1138_, v_alts_1133_, v_code_1140_, v___x_1137_, v_n_1136_);
            return v___x_1141_;
        }
        1 => {
            let mut v_code_1142_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
            v_code_1142_ = lean_ctor_get(v___x_1139_, 1);
            lean_inc_ref(v_code_1142_);
            v___x_1143_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg(v___x_1138_, v_alts_1133_, v_code_1142_, v___x_1137_, v_n_1136_);
            return v___x_1143_;
        }
        _ => {
            let mut v_code_1144_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
            v_code_1144_ = lean_ctor_get(v___x_1139_, 0);
            lean_inc_ref(v_code_1144_);
            v___x_1145_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg(v___x_1138_, v_alts_1133_, v_code_1144_, v___x_1137_, v_n_1136_);
            return v___x_1145_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___boxed(
    mut v_alts_1146_: *mut LeanObject,
    mut v_i_1147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1148_: *mut LeanObject = core::ptr::null_mut();
    v_res_1148_ =
        l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf(
            v_alts_1146_,
            v_i_1147_,
        );
    lean_dec(v_i_1147_);
    lean_dec_ref(v_alts_1146_);
    return v_res_1148_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0(
    mut v_upperBound_1149_: *mut LeanObject,
    mut v_alts_1150_: *mut LeanObject,
    mut v_code_1151_: *mut LeanObject,
    mut v_inst_1152_: *mut LeanObject,
    mut v_R_1153_: *mut LeanObject,
    mut v_a_1154_: *mut LeanObject,
    mut v_b_1155_: *mut LeanObject,
    mut v_c_1156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    v___x_1157_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg(v_upperBound_1149_, v_alts_1150_, v_code_1151_, v_a_1154_, v_b_1155_);
    return v___x_1157_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___boxed(
    mut v_upperBound_1158_: *mut LeanObject,
    mut v_alts_1159_: *mut LeanObject,
    mut v_code_1160_: *mut LeanObject,
    mut v_inst_1161_: *mut LeanObject,
    mut v_R_1162_: *mut LeanObject,
    mut v_a_1163_: *mut LeanObject,
    mut v_b_1164_: *mut LeanObject,
    mut v_c_1165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1166_: *mut LeanObject = core::ptr::null_mut();
    v_res_1166_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0(v_upperBound_1158_, v_alts_1159_, v_code_1160_, v_inst_1161_, v_R_1162_, v_a_1163_, v_b_1164_, v_c_1165_);
    lean_dec_ref(v_alts_1159_);
    lean_dec(v_upperBound_1158_);
    return v_res_1166_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___redArg(
    mut v_upperBound_1167_: *mut LeanObject,
    mut v_alts_1168_: *mut LeanObject,
    mut v_a_1169_: *mut LeanObject,
    mut v_b_1170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: u8 = 0;
    let mut v_fst_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1181_: u8 = 0;
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: u8 = 0;
    let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1191_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1176_ = lean_nat_dec_lt(v_a_1169_, v_upperBound_1167_);
                if v___x_1176_ == 0 {
                    lean_dec(v_a_1169_);
                    return v_b_1170_;
                } else {
                    v_fst_1177_ = lean_ctor_get(v_b_1170_, 0);
                    v_snd_1178_ = lean_ctor_get(v_b_1170_, 1);
                    v_isSharedCheck_1191_ = (!lean_is_exclusive(v_b_1170_)) as u8;
                    if v_isSharedCheck_1191_ == 0 {
                        v___x_1180_ = v_b_1170_;
                        v_isShared_1181_ = v_isSharedCheck_1191_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_1178_);
                        lean_inc(v_fst_1177_);
                        lean_dec(v_b_1170_);
                        v___x_1180_ = lean_box(0);
                        v_isShared_1181_ = v_isSharedCheck_1191_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1173_ = lean_unsigned_to_nat(1);
                v___x_1174_ = lean_nat_add(v_a_1169_, v___x_1173_);
                lean_dec(v_a_1169_);
                v_a_1169_ = v___x_1174_;
                v_b_1170_ = v_a_1172_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1182_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf(v_alts_1168_, v_a_1169_);
                v___x_1183_ = lean_nat_dec_lt(v_snd_1178_, v___x_1182_);
                if v___x_1183_ == 0 {
                    lean_dec(v___x_1182_);
                    if v_isShared_1181_ == 0 {
                        v___x_1185_ = v___x_1180_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_fst_1177_);
                        lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_snd_1178_);
                        v___x_1185_ = v_reuseFailAlloc_1186_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_snd_1178_);
                    lean_dec(v_fst_1177_);
                    v___x_1187_ = lean_array_fget_borrowed(v_alts_1168_, v_a_1169_);
                    lean_inc(v___x_1187_);
                    if v_isShared_1181_ == 0 {
                        lean_ctor_set(v___x_1180_, 1, v___x_1182_);
                        lean_ctor_set(v___x_1180_, 0, v___x_1187_);
                        v___x_1189_ = v___x_1180_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
                        lean_ctor_set(v_reuseFailAlloc_1190_, 1, v___x_1182_);
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
    mut v_upperBound_1192_: *mut LeanObject,
    mut v_alts_1193_: *mut LeanObject,
    mut v_a_1194_: *mut LeanObject,
    mut v_b_1195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1196_: *mut LeanObject = core::ptr::null_mut();
    v_res_1196_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___redArg(v_upperBound_1192_, v_alts_1193_, v_a_1194_, v_b_1195_);
    lean_dec_ref(v_alts_1193_);
    lean_dec(v_upperBound_1192_);
    return v_res_1196_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs(
    mut v_alts_1197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxAlt_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_max_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1210_: u8 = 0;
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1214_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1198_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0_once), _init_l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0);
                v___x_1199_ = lean_unsigned_to_nat(1);
                v___x_1200_ = lean_array_get_size(v_alts_1197_);
                v___x_1201_ = lean_unsigned_to_nat(0);
                v_maxAlt_1202_ = lean_array_get_borrowed(v___x_1198_, v_alts_1197_, v___x_1201_);
                v_max_1203_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf(v_alts_1197_, v___x_1201_);
                lean_inc(v_maxAlt_1202_);
                v___x_1204_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1204_, 0, v_maxAlt_1202_);
                lean_ctor_set(v___x_1204_, 1, v_max_1203_);
                v___x_1205_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___redArg(v___x_1200_, v_alts_1197_, v___x_1199_, v___x_1204_);
                v_fst_1206_ = lean_ctor_get(v___x_1205_, 0);
                v_snd_1207_ = lean_ctor_get(v___x_1205_, 1);
                v_isSharedCheck_1214_ = (!lean_is_exclusive(v___x_1205_)) as u8;
                if v_isSharedCheck_1214_ == 0 {
                    v___x_1209_ = v___x_1205_;
                    v_isShared_1210_ = v_isSharedCheck_1214_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_1207_);
                    lean_inc(v_fst_1206_);
                    lean_dec(v___x_1205_);
                    v___x_1209_ = lean_box(0);
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
                    v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_fst_1206_);
                    lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_snd_1207_);
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
    mut v_alts_1215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1216_: *mut LeanObject = core::ptr::null_mut();
    v_res_1216_ =
        l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs(v_alts_1215_);
    lean_dec_ref(v_alts_1215_);
    return v_res_1216_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0(
    mut v_upperBound_1217_: *mut LeanObject,
    mut v_alts_1218_: *mut LeanObject,
    mut v_inst_1219_: *mut LeanObject,
    mut v_R_1220_: *mut LeanObject,
    mut v_a_1221_: *mut LeanObject,
    mut v_b_1222_: *mut LeanObject,
    mut v_c_1223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    v___x_1224_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___redArg(v_upperBound_1217_, v_alts_1218_, v_a_1221_, v_b_1222_);
    return v___x_1224_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___boxed(
    mut v_upperBound_1225_: *mut LeanObject,
    mut v_alts_1226_: *mut LeanObject,
    mut v_inst_1227_: *mut LeanObject,
    mut v_R_1228_: *mut LeanObject,
    mut v_a_1229_: *mut LeanObject,
    mut v_b_1230_: *mut LeanObject,
    mut v_c_1231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1232_: *mut LeanObject = core::ptr::null_mut();
    v_res_1232_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0(v_upperBound_1225_, v_alts_1226_, v_inst_1227_, v_R_1228_, v_a_1229_, v_b_1230_, v_c_1231_);
    lean_dec_ref(v_alts_1226_);
    lean_dec(v_upperBound_1225_);
    return v_res_1232_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    v___x_1233_ = l_instMonadEIO(lean_box(0));
    return v___x_1233_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0(
    mut v_msg_1236_: *mut LeanObject,
    mut v___y_1237_: *mut LeanObject,
    mut v___y_1238_: *mut LeanObject,
    mut v___y_1239_: *mut LeanObject,
    mut v___y_1240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1247_: u8 = 0;
    let mut v_toFunctor_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1254_: u8 = 0;
    let mut v___f_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330__overap_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1275_: u8 = 0;
    let mut v_unused_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1277_: u8 = 0;
    let mut v_unused_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1242_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__0);
                v___x_1243_ = l_StateRefT_x27_instMonad___redArg(v___x_1242_);
                v_toApplicative_1244_ = lean_ctor_get(v___x_1243_, 0);
                v_isSharedCheck_1277_ = (!lean_is_exclusive(v___x_1243_)) as u8;
                if v_isSharedCheck_1277_ == 0 {
                    v_unused_1278_ = lean_ctor_get(v___x_1243_, 1);
                    lean_dec(v_unused_1278_);
                    v___x_1246_ = v___x_1243_;
                    v_isShared_1247_ = v_isSharedCheck_1277_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_1244_);
                    lean_dec(v___x_1243_);
                    v___x_1246_ = lean_box(0);
                    v_isShared_1247_ = v_isSharedCheck_1277_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1248_ = lean_ctor_get(v_toApplicative_1244_, 0);
                v_toSeq_1249_ = lean_ctor_get(v_toApplicative_1244_, 2);
                v_toSeqLeft_1250_ = lean_ctor_get(v_toApplicative_1244_, 3);
                v_toSeqRight_1251_ = lean_ctor_get(v_toApplicative_1244_, 4);
                v_isSharedCheck_1275_ = (!lean_is_exclusive(v_toApplicative_1244_)) as u8;
                if v_isSharedCheck_1275_ == 0 {
                    v_unused_1276_ = lean_ctor_get(v_toApplicative_1244_, 1);
                    lean_dec(v_unused_1276_);
                    v___x_1253_ = v_toApplicative_1244_;
                    v_isShared_1254_ = v_isSharedCheck_1275_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_1251_);
                    lean_inc(v_toSeqLeft_1250_);
                    lean_inc(v_toSeq_1249_);
                    lean_inc(v_toFunctor_1248_);
                    lean_dec(v_toApplicative_1244_);
                    v___x_1253_ = lean_box(0);
                    v_isShared_1254_ = v_isSharedCheck_1275_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1255_ = l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__1;
                v___f_1256_ = l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__2;
                lean_inc_ref(v_toFunctor_1248_);
                v___f_1257_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1257_, 0, v_toFunctor_1248_);
                v___f_1258_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1258_, 0, v_toFunctor_1248_);
                v___x_1259_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1259_, 0, v___f_1257_);
                lean_ctor_set(v___x_1259_, 1, v___f_1258_);
                v___f_1260_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1260_, 0, v_toSeqRight_1251_);
                v___f_1261_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1261_, 0, v_toSeqLeft_1250_);
                v___f_1262_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1262_, 0, v_toSeq_1249_);
                if v_isShared_1254_ == 0 {
                    lean_ctor_set(v___x_1253_, 4, v___f_1260_);
                    lean_ctor_set(v___x_1253_, 3, v___f_1261_);
                    lean_ctor_set(v___x_1253_, 2, v___f_1262_);
                    lean_ctor_set(v___x_1253_, 1, v___f_1255_);
                    lean_ctor_set(v___x_1253_, 0, v___x_1259_);
                    v___x_1264_ = v___x_1253_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1259_);
                    lean_ctor_set(v_reuseFailAlloc_1274_, 1, v___f_1255_);
                    lean_ctor_set(v_reuseFailAlloc_1274_, 2, v___f_1262_);
                    lean_ctor_set(v_reuseFailAlloc_1274_, 3, v___f_1261_);
                    lean_ctor_set(v_reuseFailAlloc_1274_, 4, v___f_1260_);
                    v___x_1264_ = v_reuseFailAlloc_1274_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1247_ == 0 {
                    lean_ctor_set(v___x_1246_, 1, v___f_1256_);
                    lean_ctor_set(v___x_1246_, 0, v___x_1264_);
                    v___x_1266_ = v___x_1246_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1264_);
                    lean_ctor_set(v_reuseFailAlloc_1273_, 1, v___f_1256_);
                    v___x_1266_ = v_reuseFailAlloc_1273_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1267_ = l_StateRefT_x27_instMonad___redArg(v___x_1266_);
                v___x_1268_ = lean_box(0);
                v___x_1269_ = l_instInhabitedOfMonad___redArg(v___x_1267_, v___x_1268_);
                v___f_1270_ = lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_1270_, 0, v___x_1269_);
                v___x_2330__overap_1271_ = lean_panic_fn_borrowed(v___f_1270_, v_msg_1236_);
                lean_dec_ref(v___f_1270_);
                lean_inc(v___y_1240_);
                lean_inc_ref(v___y_1239_);
                lean_inc(v___y_1238_);
                lean_inc_ref(v___y_1237_);
                v___x_1272_ = lean_apply_5(
                    v___x_2330__overap_1271_,
                    v___y_1237_,
                    v___y_1238_,
                    v___y_1239_,
                    v___y_1240_,
                    lean_box(0),
                );
                return v___x_1272_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___boxed(
    mut v_msg_1279_: *mut LeanObject,
    mut v___y_1280_: *mut LeanObject,
    mut v___y_1281_: *mut LeanObject,
    mut v___y_1282_: *mut LeanObject,
    mut v___y_1283_: *mut LeanObject,
    mut v___y_1284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1285_: *mut LeanObject = core::ptr::null_mut();
    v_res_1285_ = l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0(v_msg_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
    lean_dec(v___y_1283_);
    lean_dec_ref(v___y_1282_);
    lean_dec(v___y_1281_);
    lean_dec_ref(v___y_1280_);
    return v_res_1285_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3()
-> *mut LeanObject {
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    v___x_1289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__2;
    v___x_1290_ = lean_unsigned_to_nat(36);
    v___x_1291_ = lean_unsigned_to_nat(77);
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
    mut v_snd_1295_: *mut LeanObject,
    mut v_fst_1296_: *mut LeanObject,
    mut v_as_1297_: *mut LeanObject,
    mut v_sz_1298_: usize,
    mut v_i_1299_: usize,
    mut v_b_1300_: *mut LeanObject,
    mut v___y_1301_: *mut LeanObject,
    mut v___y_1302_: *mut LeanObject,
    mut v___y_1303_: *mut LeanObject,
    mut v___y_1304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: usize = 0;
    let mut v___x_1309_: usize = 0;
    let mut v___x_1311_: u8 = 0;
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1317_: u8 = 0;
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: u8 = 0;
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: u8 = 0;
    let mut v___y_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: u8 = 0;
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: u8 = 0;
    let mut v_code_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1339_: u8 = 0;
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1343_: u8 = 0;
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1350_: u8 = 0;
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1354_: u8 = 0;
    let mut v___y_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1363_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1311_ = lean_usize_dec_lt(v_i_1299_, v_sz_1298_);
                if v___x_1311_ == 0 {
                    lean_dec_ref(v_fst_1296_);
                    v___x_1312_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1312_, 0, v_b_1300_);
                    return v___x_1312_;
                } else {
                    v_fst_1313_ = lean_ctor_get(v_b_1300_, 0);
                    v_snd_1314_ = lean_ctor_get(v_b_1300_, 1);
                    v_isSharedCheck_1363_ = (!lean_is_exclusive(v_b_1300_)) as u8;
                    if v_isSharedCheck_1363_ == 0 {
                        v___x_1316_ = v_b_1300_;
                        v_isShared_1317_ = v_isSharedCheck_1363_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_1314_);
                        lean_inc(v_fst_1313_);
                        lean_dec(v_b_1300_);
                        v___x_1316_ = lean_box(0);
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
                v___x_1318_ = lean_unsigned_to_nat(1);
                v___x_1319_ = lean_nat_dec_eq(v_snd_1295_, v___x_1318_);
                v_a_1325_ = lean_array_uget_borrowed(v_as_1297_, v_i_1299_);
                v___x_1326_ = 1;
                match lean_obj_tag(v_a_1325_) {
                    0 => {
                        v_code_1360_ = lean_ctor_get(v_a_1325_, 2);
                        lean_inc_ref(v_code_1360_);
                        v___y_1356_ = v_code_1360_;
                        state = 10;
                        continue;
                    }
                    1 => {
                        v_code_1361_ = lean_ctor_get(v_a_1325_, 1);
                        lean_inc_ref(v_code_1361_);
                        v___y_1356_ = v_code_1361_;
                        state = 10;
                        continue;
                    }
                    _ => {
                        v_code_1362_ = lean_ctor_get(v_a_1325_, 0);
                        lean_inc_ref(v_code_1362_);
                        v___y_1356_ = v_code_1362_;
                        state = 10;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1321_ = lean_box((v___x_1319_) as usize);
                if v_isShared_1317_ == 0 {
                    lean_ctor_set(v___x_1316_, 1, v___x_1321_);
                    v___x_1323_ = v___x_1316_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_fst_1313_);
                    lean_ctor_set(v_reuseFailAlloc_1324_, 1, v___x_1321_);
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
                    lean_del_object(v___x_1316_);
                    lean_inc(v_a_1325_);
                    v___x_1331_ = lean_array_push(v_fst_1313_, v_a_1325_);
                    v___x_1332_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1332_, 0, v___x_1331_);
                    lean_ctor_set(v___x_1332_, 1, v_snd_1314_);
                    v_a_1307_ = v___x_1332_;
                    state = 1;
                    continue;
                } else {
                    if lean_obj_tag(v_a_1325_) == 1 {
                        v___x_1333_ = (lean_unbox(v_snd_1314_) as u8);
                        lean_dec(v_snd_1314_);
                        if v___x_1333_ == 0 {
                            v_code_1334_ = lean_ctor_get(v_a_1325_, 1);
                            v___x_1335_ = l_Lean_Compiler_LCNF_eraseCode___redArg(
                                v___x_1326_,
                                v_code_1334_,
                                v___y_1302_,
                            );
                            if lean_obj_tag(v___x_1335_) == 0 {
                                lean_dec_ref_known(v___x_1335_, 1);
                                state = 3;
                                continue;
                            } else {
                                lean_del_object(v___x_1316_);
                                lean_dec(v_fst_1313_);
                                lean_dec_ref(v_fst_1296_);
                                v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
                                v_isSharedCheck_1343_ = (!lean_is_exclusive(v___x_1335_)) as u8;
                                if v_isSharedCheck_1343_ == 0 {
                                    v___x_1338_ = v___x_1335_;
                                    v_isShared_1339_ = v_isSharedCheck_1343_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_1336_);
                                    lean_dec(v___x_1335_);
                                    v___x_1338_ = lean_box(0);
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
                        lean_del_object(v___x_1316_);
                        v___x_1344_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3);
                        v___x_1345_ = l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0(v___x_1344_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
                        if lean_obj_tag(v___x_1345_) == 0 {
                            lean_dec_ref_known(v___x_1345_, 1);
                            v___x_1346_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_1346_, 0, v_fst_1313_);
                            lean_ctor_set(v___x_1346_, 1, v_snd_1314_);
                            v_a_1307_ = v___x_1346_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_snd_1314_);
                            lean_dec(v_fst_1313_);
                            lean_dec_ref(v_fst_1296_);
                            v_a_1347_ = lean_ctor_get(v___x_1345_, 0);
                            v_isSharedCheck_1354_ = (!lean_is_exclusive(v___x_1345_)) as u8;
                            if v_isSharedCheck_1354_ == 0 {
                                v___x_1349_ = v___x_1345_;
                                v_isShared_1350_ = v_isSharedCheck_1354_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_1347_);
                                lean_dec(v___x_1345_);
                                v___x_1349_ = lean_box(0);
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
                    v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
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
                    v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
                    v___x_1352_ = v_reuseFailAlloc_1353_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1352_;
            }
            10 => match lean_obj_tag(v_fst_1296_) {
                0 => {
                    v_code_1357_ = lean_ctor_get(v_fst_1296_, 2);
                    lean_inc_ref(v_code_1357_);
                    v___y_1328_ = v___y_1356_;
                    v___y_1329_ = v_code_1357_;
                    state = 5;
                    continue;
                }
                1 => {
                    v_code_1358_ = lean_ctor_get(v_fst_1296_, 1);
                    lean_inc_ref(v_code_1358_);
                    v___y_1328_ = v___y_1356_;
                    v___y_1329_ = v_code_1358_;
                    state = 5;
                    continue;
                }
                _ => {
                    v_code_1359_ = lean_ctor_get(v_fst_1296_, 0);
                    lean_inc_ref(v_code_1359_);
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
    mut v_snd_1364_: *mut LeanObject,
    mut v_fst_1365_: *mut LeanObject,
    mut v_as_1366_: *mut LeanObject,
    mut v_sz_1367_: *mut LeanObject,
    mut v_i_1368_: *mut LeanObject,
    mut v_b_1369_: *mut LeanObject,
    mut v___y_1370_: *mut LeanObject,
    mut v___y_1371_: *mut LeanObject,
    mut v___y_1372_: *mut LeanObject,
    mut v___y_1373_: *mut LeanObject,
    mut v___y_1374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1375_: usize = 0;
    let mut v_i_boxed_1376_: usize = 0;
    let mut v_res_1377_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1375_ = lean_unbox_usize(v_sz_1367_);
    lean_dec(v_sz_1367_);
    v_i_boxed_1376_ = lean_unbox_usize(v_i_1368_);
    lean_dec(v_i_1368_);
    v_res_1377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1(v_snd_1364_, v_fst_1365_, v_as_1366_, v_sz_boxed_1375_, v_i_boxed_1376_, v_b_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
    lean_dec(v___y_1373_);
    lean_dec_ref(v___y_1372_);
    lean_dec(v___y_1371_);
    lean_dec_ref(v___y_1370_);
    lean_dec_ref(v_as_1366_);
    lean_dec(v_snd_1364_);
    return v_res_1377_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__2(
    mut v___x_1378_: *mut LeanObject,
    mut v_as_1379_: *mut LeanObject,
    mut v_i_1380_: usize,
    mut v_stop_1381_: usize,
) -> u8 {
    let mut v___x_1382_: u8 = 0;
    let mut v___x_1383_: u8 = 0;
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
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
                    if lean_obj_tag(v___x_1384_) == 2 {
                        return v___x_1383_;
                    } else {
                        v___x_1385_ = lean_unsigned_to_nat(1);
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
    mut v___x_1391_: *mut LeanObject,
    mut v_as_1392_: *mut LeanObject,
    mut v_i_1393_: *mut LeanObject,
    mut v_stop_1394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1395_: usize = 0;
    let mut v_stop_boxed_1396_: usize = 0;
    let mut v_res_1397_: u8 = 0;
    let mut v_r_1398_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1395_ = lean_unbox_usize(v_i_1393_);
    lean_dec(v_i_1393_);
    v_stop_boxed_1396_ = lean_unbox_usize(v_stop_1394_);
    lean_dec(v_stop_1394_);
    v_res_1397_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__2(v___x_1391_, v_as_1392_, v_i_boxed_1395_, v_stop_boxed_1396_);
    lean_dec_ref(v_as_1392_);
    lean_dec(v___x_1391_);
    v_r_1398_ = lean_box((v_res_1397_) as usize);
    return v_r_1398_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt(
    mut v_alts_1405_: *mut LeanObject,
    mut v_a_1406_: *mut LeanObject,
    mut v_a_1407_: *mut LeanObject,
    mut v_a_1408_: *mut LeanObject,
    mut v_a_1409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1420_: u8 = 0;
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: u8 = 0;
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1426_: usize = 0;
    let mut v___x_1427_: usize = 0;
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1439_: u8 = 0;
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1443_: u8 = 0;
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: u8 = 0;
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: u8 = 0;
    let mut v___x_1449_: usize = 0;
    let mut v___x_1450_: usize = 0;
    let mut v___x_1451_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1417_ = lean_array_get_size(v_alts_1405_);
                v___x_1418_ = lean_unsigned_to_nat(1);
                v___x_1446_ = lean_nat_dec_le(v___x_1417_, v___x_1418_);
                if v___x_1446_ == 0 {
                    v___x_1447_ = lean_unsigned_to_nat(0);
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
                v___x_1414_ = lean_alloc_ctor(2, 1, (0) as u32);
                lean_ctor_set(v___x_1414_, 0, v___y_1413_);
                v___x_1415_ = lean_array_push(v___y_1412_, v___x_1414_);
                v___x_1416_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1416_, 0, v___x_1415_);
                return v___x_1416_;
            }
            2 => {
                if v___y_1420_ == 0 {
                    v___x_1421_ =
                        l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs(
                            v_alts_1405_,
                        );
                    v_fst_1422_ = lean_ctor_get(v___x_1421_, 0);
                    lean_inc(v_fst_1422_);
                    v_snd_1423_ = lean_ctor_get(v___x_1421_, 1);
                    lean_inc(v_snd_1423_);
                    lean_dec_ref(v___x_1421_);
                    v___x_1424_ = lean_nat_dec_eq(v_snd_1423_, v___x_1418_);
                    if v___x_1424_ == 0 {
                        v___x_1425_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__1;
                        v_sz_1426_ = lean_array_size(v_alts_1405_);
                        v___x_1427_ = 0usize;
                        lean_inc(v_fst_1422_);
                        v___x_1428_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1(v_snd_1423_, v_fst_1422_, v_alts_1405_, v_sz_1426_, v___x_1427_, v___x_1425_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_);
                        lean_dec_ref(v_alts_1405_);
                        lean_dec(v_snd_1423_);
                        if lean_obj_tag(v___x_1428_) == 0 {
                            v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
                            lean_inc(v_a_1429_);
                            lean_dec_ref_known(v___x_1428_, 1);
                            match lean_obj_tag(v_fst_1422_) {
                                0 => {
                                    v_fst_1430_ = lean_ctor_get(v_a_1429_, 0);
                                    lean_inc(v_fst_1430_);
                                    lean_dec(v_a_1429_);
                                    v_code_1431_ = lean_ctor_get(v_fst_1422_, 2);
                                    lean_inc_ref(v_code_1431_);
                                    lean_dec_ref_known(v_fst_1422_, 3);
                                    v___y_1412_ = v_fst_1430_;
                                    v___y_1413_ = v_code_1431_;
                                    state = 1;
                                    continue;
                                }
                                1 => {
                                    v_fst_1432_ = lean_ctor_get(v_a_1429_, 0);
                                    lean_inc(v_fst_1432_);
                                    lean_dec(v_a_1429_);
                                    v_code_1433_ = lean_ctor_get(v_fst_1422_, 1);
                                    lean_inc_ref(v_code_1433_);
                                    lean_dec_ref_known(v_fst_1422_, 2);
                                    v___y_1412_ = v_fst_1432_;
                                    v___y_1413_ = v_code_1433_;
                                    state = 1;
                                    continue;
                                }
                                _ => {
                                    v_fst_1434_ = lean_ctor_get(v_a_1429_, 0);
                                    lean_inc(v_fst_1434_);
                                    lean_dec(v_a_1429_);
                                    v_code_1435_ = lean_ctor_get(v_fst_1422_, 0);
                                    lean_inc_ref(v_code_1435_);
                                    lean_dec_ref_known(v_fst_1422_, 1);
                                    v___y_1412_ = v_fst_1434_;
                                    v___y_1413_ = v_code_1435_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_fst_1422_);
                            v_a_1436_ = lean_ctor_get(v___x_1428_, 0);
                            v_isSharedCheck_1443_ = (!lean_is_exclusive(v___x_1428_)) as u8;
                            if v_isSharedCheck_1443_ == 0 {
                                v___x_1438_ = v___x_1428_;
                                v_isShared_1439_ = v_isSharedCheck_1443_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_1436_);
                                lean_dec(v___x_1428_);
                                v___x_1438_ = lean_box(0);
                                v_isShared_1439_ = v_isSharedCheck_1443_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_snd_1423_);
                        lean_dec(v_fst_1422_);
                        v___x_1444_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1444_, 0, v_alts_1405_);
                        return v___x_1444_;
                    }
                } else {
                    v___x_1445_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1445_, 0, v_alts_1405_);
                    return v___x_1445_;
                }
            }
            3 => {
                if v_isShared_1439_ == 0 {
                    v___x_1441_ = v___x_1438_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
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
    mut v_alts_1452_: *mut LeanObject,
    mut v_a_1453_: *mut LeanObject,
    mut v_a_1454_: *mut LeanObject,
    mut v_a_1455_: *mut LeanObject,
    mut v_a_1456_: *mut LeanObject,
    mut v_a_1457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1458_: *mut LeanObject = core::ptr::null_mut();
    v_res_1458_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt(
        v_alts_1452_,
        v_a_1453_,
        v_a_1454_,
        v_a_1455_,
        v_a_1456_,
    );
    lean_dec(v_a_1456_);
    lean_dec_ref(v_a_1455_);
    lean_dec(v_a_1454_);
    lean_dec_ref(v_a_1453_);
    return v_res_1458_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0(
    mut v_as_1459_: *mut LeanObject,
    mut v_i_1460_: usize,
    mut v_stop_1461_: usize,
    mut v_b_1462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: usize = 0;
    let mut v___x_1466_: usize = 0;
    let mut v___x_1468_: u8 = 0;
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1468_ = lean_usize_dec_eq(v_i_1460_, v_stop_1461_);
                if v___x_1468_ == 0 {
                    v___x_1469_ = lean_array_uget_borrowed(v_as_1459_, v_i_1460_);
                    match lean_obj_tag(v___x_1469_) {
                        0 => {
                            v_code_1473_ = lean_ctor_get(v___x_1469_, 2);
                            lean_inc_ref(v_code_1473_);
                            v___y_1471_ = v_code_1473_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_code_1474_ = lean_ctor_get(v___x_1469_, 1);
                            lean_inc_ref(v_code_1474_);
                            v___y_1471_ = v_code_1474_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            v_code_1475_ = lean_ctor_get(v___x_1469_, 0);
                            lean_inc_ref(v_code_1475_);
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
                if lean_obj_tag(v___y_1471_) == 6 {
                    lean_dec_ref_known(v___y_1471_, 1);
                    v___y_1464_ = v_b_1462_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v___y_1471_);
                    lean_inc(v___x_1469_);
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
    mut v_as_1476_: *mut LeanObject,
    mut v_i_1477_: *mut LeanObject,
    mut v_stop_1478_: *mut LeanObject,
    mut v_b_1479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1480_: usize = 0;
    let mut v_stop_boxed_1481_: usize = 0;
    let mut v_res_1482_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1480_ = lean_unbox_usize(v_i_1477_);
    lean_dec(v_i_1477_);
    v_stop_boxed_1481_ = lean_unbox_usize(v_stop_1478_);
    lean_dec(v_stop_1478_);
    v_res_1482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0(v_as_1476_, v_i_boxed_1480_, v_stop_boxed_1481_, v_b_1479_);
    lean_dec_ref(v_as_1476_);
    return v_res_1482_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable(
    mut v_alts_1483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: u8 = 0;
    v___x_1484_ = lean_unsigned_to_nat(0);
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
                let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
                v___x_1489_ = 0usize;
                v___x_1490_ = lean_usize_of_nat(v___x_1485_);
                v___x_1491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0(v_alts_1483_, v___x_1489_, v___x_1490_, v___x_1486_);
                return v___x_1491_;
            }
        } else {
            let mut v___x_1492_: usize = 0;
            let mut v___x_1493_: usize = 0;
            let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
            v___x_1492_ = 0usize;
            v___x_1493_ = lean_usize_of_nat(v___x_1485_);
            v___x_1494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0(v_alts_1483_, v___x_1492_, v___x_1493_, v___x_1486_);
            return v___x_1494_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable___boxed(
    mut v_alts_1495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1496_: *mut LeanObject = core::ptr::null_mut();
    v_res_1496_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable(
        v_alts_1495_,
    );
    lean_dec_ref(v_alts_1495_);
    return v_res_1496_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases(
    mut v_c_1497_: *mut LeanObject,
    mut v_a_1498_: *mut LeanObject,
    mut v_a_1499_: *mut LeanObject,
    mut v_a_1500_: *mut LeanObject,
    mut v_a_1501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_typeName_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_resultType_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discr_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1509_: u8 = 0;
    let mut v_alts_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1515_: u8 = 0;
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: u8 = 0;
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: u8 = 0;
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1545_: u8 = 0;
    let mut v_a_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1549_: u8 = 0;
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1553_: u8 = 0;
    let mut v_isSharedCheck_1554_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_typeName_1503_ = lean_ctor_get(v_c_1497_, 0);
                v_resultType_1504_ = lean_ctor_get(v_c_1497_, 1);
                v_discr_1505_ = lean_ctor_get(v_c_1497_, 2);
                v_alts_1506_ = lean_ctor_get(v_c_1497_, 3);
                v_isSharedCheck_1554_ = (!lean_is_exclusive(v_c_1497_)) as u8;
                if v_isSharedCheck_1554_ == 0 {
                    v___x_1508_ = v_c_1497_;
                    v_isShared_1509_ = v_isSharedCheck_1554_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_alts_1506_);
                    lean_inc(v_discr_1505_);
                    lean_inc(v_resultType_1504_);
                    lean_inc(v_typeName_1503_);
                    lean_dec(v_c_1497_);
                    v___x_1508_ = lean_box(0);
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
                lean_dec_ref(v_alts_1506_);
                v___x_1511_ =
                    l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt(
                        v_alts_1510_,
                        v_a_1498_,
                        v_a_1499_,
                        v_a_1500_,
                        v_a_1501_,
                    );
                if lean_obj_tag(v___x_1511_) == 0 {
                    v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
                    v_isSharedCheck_1545_ = (!lean_is_exclusive(v___x_1511_)) as u8;
                    if v_isSharedCheck_1545_ == 0 {
                        v___x_1514_ = v___x_1511_;
                        v_isShared_1515_ = v_isSharedCheck_1545_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1512_);
                        lean_dec(v___x_1511_);
                        v___x_1514_ = lean_box(0);
                        v_isShared_1515_ = v_isSharedCheck_1545_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1508_);
                    lean_dec(v_discr_1505_);
                    lean_dec_ref(v_resultType_1504_);
                    lean_dec(v_typeName_1503_);
                    v_a_1546_ = lean_ctor_get(v___x_1511_, 0);
                    v_isSharedCheck_1553_ = (!lean_is_exclusive(v___x_1511_)) as u8;
                    if v_isSharedCheck_1553_ == 0 {
                        v___x_1548_ = v___x_1511_;
                        v_isShared_1549_ = v_isSharedCheck_1553_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_1546_);
                        lean_dec(v___x_1511_);
                        v___x_1548_ = lean_box(0);
                        v_isShared_1549_ = v_isSharedCheck_1553_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1516_ = lean_array_get_size(v_a_1512_);
                v___x_1517_ = lean_unsigned_to_nat(0);
                v___x_1518_ = lean_nat_dec_eq(v___x_1516_, v___x_1517_);
                if v___x_1518_ == 0 {
                    v___x_1519_ = lean_unsigned_to_nat(1);
                    v___x_1520_ = lean_nat_dec_eq(v___x_1516_, v___x_1519_);
                    if v___x_1520_ == 0 {
                        if v_isShared_1509_ == 0 {
                            lean_ctor_set(v___x_1508_, 3, v_a_1512_);
                            v___x_1522_ = v___x_1508_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_typeName_1503_);
                            lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_resultType_1504_);
                            lean_ctor_set(v_reuseFailAlloc_1527_, 2, v_discr_1505_);
                            lean_ctor_set(v_reuseFailAlloc_1527_, 3, v_a_1512_);
                            v___x_1522_ = v_reuseFailAlloc_1527_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_1508_);
                        lean_dec(v_discr_1505_);
                        lean_dec_ref(v_resultType_1504_);
                        lean_dec(v_typeName_1503_);
                        v___x_1528_ = lean_array_fget(v_a_1512_, v___x_1517_);
                        lean_dec(v_a_1512_);
                        match lean_obj_tag(v___x_1528_) {
                            0 => {
                                v_code_1529_ = lean_ctor_get(v___x_1528_, 2);
                                lean_inc_ref(v_code_1529_);
                                lean_dec_ref_known(v___x_1528_, 3);
                                if v_isShared_1515_ == 0 {
                                    lean_ctor_set(v___x_1514_, 0, v_code_1529_);
                                    v___x_1531_ = v___x_1514_;
                                    state = 5;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_code_1529_);
                                    v___x_1531_ = v_reuseFailAlloc_1532_;
                                    state = 5;
                                    continue;
                                }
                            }
                            1 => {
                                v_code_1533_ = lean_ctor_get(v___x_1528_, 1);
                                lean_inc_ref(v_code_1533_);
                                lean_dec_ref_known(v___x_1528_, 2);
                                if v_isShared_1515_ == 0 {
                                    lean_ctor_set(v___x_1514_, 0, v_code_1533_);
                                    v___x_1535_ = v___x_1514_;
                                    state = 6;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_code_1533_);
                                    v___x_1535_ = v_reuseFailAlloc_1536_;
                                    state = 6;
                                    continue;
                                }
                            }
                            _ => {
                                v_code_1537_ = lean_ctor_get(v___x_1528_, 0);
                                lean_inc_ref(v_code_1537_);
                                lean_dec_ref_known(v___x_1528_, 1);
                                if v_isShared_1515_ == 0 {
                                    lean_ctor_set(v___x_1514_, 0, v_code_1537_);
                                    v___x_1539_ = v___x_1514_;
                                    state = 7;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_code_1537_);
                                    v___x_1539_ = v_reuseFailAlloc_1540_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec(v_a_1512_);
                    lean_del_object(v___x_1508_);
                    lean_dec(v_discr_1505_);
                    lean_dec(v_typeName_1503_);
                    v___x_1541_ = lean_alloc_ctor(6, 1, (0) as u32);
                    lean_ctor_set(v___x_1541_, 0, v_resultType_1504_);
                    if v_isShared_1515_ == 0 {
                        lean_ctor_set(v___x_1514_, 0, v___x_1541_);
                        v___x_1543_ = v___x_1514_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
                        v___x_1543_ = v_reuseFailAlloc_1544_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1523_ = lean_alloc_ctor(4, 1, (0) as u32);
                lean_ctor_set(v___x_1523_, 0, v___x_1522_);
                if v_isShared_1515_ == 0 {
                    lean_ctor_set(v___x_1514_, 0, v___x_1523_);
                    v___x_1525_ = v___x_1514_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1523_);
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
                    v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
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
    mut v_c_1555_: *mut LeanObject,
    mut v_a_1556_: *mut LeanObject,
    mut v_a_1557_: *mut LeanObject,
    mut v_a_1558_: *mut LeanObject,
    mut v_a_1559_: *mut LeanObject,
    mut v_a_1560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1561_: *mut LeanObject = core::ptr::null_mut();
    v_res_1561_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases(
        v_c_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_,
    );
    lean_dec(v_a_1559_);
    lean_dec_ref(v_a_1558_);
    lean_dec(v_a_1557_);
    lean_dec_ref(v_a_1556_);
    return v_res_1561_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg(
    mut v_alt_1562_: *mut LeanObject,
    mut v_f_1563_: *mut LeanObject,
    mut v___y_1564_: *mut LeanObject,
    mut v___y_1565_: *mut LeanObject,
    mut v___y_1566_: *mut LeanObject,
    mut v___y_1567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1575_: u8 = 0;
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1580_: u8 = 0;
    let mut v_a_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1584_: u8 = 0;
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1588_: u8 = 0;
    let mut v_code_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_alt_1562_) {
                0 => {
                    v_code_1589_ = lean_ctor_get(v_alt_1562_, 2);
                    lean_inc_ref(v_code_1589_);
                    v___y_1570_ = v_code_1589_;
                    state = 1;
                    continue;
                }
                1 => {
                    v_code_1590_ = lean_ctor_get(v_alt_1562_, 1);
                    lean_inc_ref(v_code_1590_);
                    v___y_1570_ = v_code_1590_;
                    state = 1;
                    continue;
                }
                _ => {
                    v_code_1591_ = lean_ctor_get(v_alt_1562_, 0);
                    lean_inc_ref(v_code_1591_);
                    v___y_1570_ = v_code_1591_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                lean_inc(v___y_1567_);
                lean_inc_ref(v___y_1566_);
                lean_inc(v___y_1565_);
                lean_inc_ref(v___y_1564_);
                v___x_1571_ = lean_apply_6(
                    v_f_1563_,
                    v___y_1570_,
                    v___y_1564_,
                    v___y_1565_,
                    v___y_1566_,
                    v___y_1567_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1571_) == 0 {
                    v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
                    v_isSharedCheck_1580_ = (!lean_is_exclusive(v___x_1571_)) as u8;
                    if v_isSharedCheck_1580_ == 0 {
                        v___x_1574_ = v___x_1571_;
                        v_isShared_1575_ = v_isSharedCheck_1580_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1572_);
                        lean_dec(v___x_1571_);
                        v___x_1574_ = lean_box(0);
                        v_isShared_1575_ = v_isSharedCheck_1580_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_alt_1562_);
                    v_a_1581_ = lean_ctor_get(v___x_1571_, 0);
                    v_isSharedCheck_1588_ = (!lean_is_exclusive(v___x_1571_)) as u8;
                    if v_isSharedCheck_1588_ == 0 {
                        v___x_1583_ = v___x_1571_;
                        v_isShared_1584_ = v_isSharedCheck_1588_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1581_);
                        lean_dec(v___x_1571_);
                        v___x_1583_ = lean_box(0);
                        v_isShared_1584_ = v_isSharedCheck_1588_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1576_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_1562_, v_a_1572_);
                if v_isShared_1575_ == 0 {
                    lean_ctor_set(v___x_1574_, 0, v___x_1576_);
                    v___x_1578_ = v___x_1574_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
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
                    v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1581_);
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
    mut v_alt_1592_: *mut LeanObject,
    mut v_f_1593_: *mut LeanObject,
    mut v___y_1594_: *mut LeanObject,
    mut v___y_1595_: *mut LeanObject,
    mut v___y_1596_: *mut LeanObject,
    mut v___y_1597_: *mut LeanObject,
    mut v___y_1598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1599_: *mut LeanObject = core::ptr::null_mut();
    v_res_1599_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg(v_alt_1592_, v_f_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
    lean_dec(v___y_1597_);
    lean_dec_ref(v___y_1596_);
    lean_dec(v___y_1595_);
    lean_dec_ref(v___y_1594_);
    return v_res_1599_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0(
    mut v_pu_1600_: u8,
    mut v_alt_1601_: *mut LeanObject,
    mut v_f_1602_: *mut LeanObject,
    mut v___y_1603_: *mut LeanObject,
    mut v___y_1604_: *mut LeanObject,
    mut v___y_1605_: *mut LeanObject,
    mut v___y_1606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    v___x_1608_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg(v_alt_1601_, v_f_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
    return v___x_1608_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___boxed(
    mut v_pu_1609_: *mut LeanObject,
    mut v_alt_1610_: *mut LeanObject,
    mut v_f_1611_: *mut LeanObject,
    mut v___y_1612_: *mut LeanObject,
    mut v___y_1613_: *mut LeanObject,
    mut v___y_1614_: *mut LeanObject,
    mut v___y_1615_: *mut LeanObject,
    mut v___y_1616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1617_: u8 = 0;
    let mut v_res_1618_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1617_ = (lean_unbox(v_pu_1609_) as u8);
    v_res_1618_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0(v_pu_boxed_1617_, v_alt_1610_, v_f_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
    lean_dec(v___y_1615_);
    lean_dec_ref(v___y_1614_);
    lean_dec(v___y_1613_);
    lean_dec_ref(v___y_1612_);
    return v_res_1618_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(
    mut v_code_1619_: *mut LeanObject,
    mut v_a_1620_: *mut LeanObject,
    mut v_a_1621_: *mut LeanObject,
    mut v_a_1622_: *mut LeanObject,
    mut v_a_1623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decl_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1631_: u8 = 0;
    let mut v___x_1632_: usize = 0;
    let mut v___x_1633_: usize = 0;
    let mut v___x_1634_: u8 = 0;
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1637_: u8 = 0;
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1644_: u8 = 0;
    let mut v_unused_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1650_: u8 = 0;
    let mut v_decl_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: u8 = 0;
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1665_: u8 = 0;
    let mut v___y_1667_: u8 = 0;
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1670_: u8 = 0;
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1677_: u8 = 0;
    let mut v_unused_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: usize = 0;
    let mut v___x_1684_: usize = 0;
    let mut v___x_1685_: u8 = 0;
    let mut v___x_1686_: usize = 0;
    let mut v___x_1687_: usize = 0;
    let mut v___x_1688_: u8 = 0;
    let mut v_isSharedCheck_1689_: u8 = 0;
    let mut v_a_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1693_: u8 = 0;
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1697_: u8 = 0;
    let mut v_cases_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_resultType_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discr_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1705_: u8 = 0;
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1716_: u8 = 0;
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1720_: u8 = 0;
    let mut v_isSharedCheck_1721_: u8 = 0;
    let mut v_fvarId_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1730_: u8 = 0;
    let mut v___x_1731_: usize = 0;
    let mut v___x_1732_: usize = 0;
    let mut v___x_1733_: u8 = 0;
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1736_: u8 = 0;
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1743_: u8 = 0;
    let mut v_unused_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1751_: u8 = 0;
    let mut v_fvarId_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1760_: u8 = 0;
    let mut v___x_1761_: usize = 0;
    let mut v___x_1762_: usize = 0;
    let mut v___x_1763_: u8 = 0;
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1766_: u8 = 0;
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1773_: u8 = 0;
    let mut v_unused_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1781_: u8 = 0;
    let mut v_fvarId_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1792_: u8 = 0;
    let mut v___x_1793_: usize = 0;
    let mut v___x_1794_: usize = 0;
    let mut v___x_1795_: u8 = 0;
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1798_: u8 = 0;
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1805_: u8 = 0;
    let mut v_unused_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1815_: u8 = 0;
    let mut v_fvarId_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cidx_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1823_: u8 = 0;
    let mut v___x_1824_: usize = 0;
    let mut v___x_1825_: usize = 0;
    let mut v___x_1826_: u8 = 0;
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1829_: u8 = 0;
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1836_: u8 = 0;
    let mut v_unused_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1843_: u8 = 0;
    let mut v_fvarId_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_check_1846_: u8 = 0;
    let mut v_persistent_1847_: u8 = 0;
    let mut v_k_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1853_: u8 = 0;
    let mut v___x_1854_: usize = 0;
    let mut v___x_1855_: usize = 0;
    let mut v___x_1856_: u8 = 0;
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1859_: u8 = 0;
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1866_: u8 = 0;
    let mut v_unused_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1873_: u8 = 0;
    let mut v_fvarId_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_check_1876_: u8 = 0;
    let mut v_persistent_1877_: u8 = 0;
    let mut v_objs_x3f_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1884_: u8 = 0;
    let mut v___x_1885_: usize = 0;
    let mut v___x_1886_: usize = 0;
    let mut v___x_1887_: u8 = 0;
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1890_: u8 = 0;
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1897_: u8 = 0;
    let mut v_unused_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1905_: u8 = 0;
    let mut v_fvarId_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1912_: u8 = 0;
    let mut v___x_1913_: usize = 0;
    let mut v___x_1914_: usize = 0;
    let mut v___x_1915_: u8 = 0;
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1918_: u8 = 0;
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1925_: u8 = 0;
    let mut v_unused_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1931_: u8 = 0;
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match lean_obj_tag(v_code_1619_) {
                    0 => {
                        v_decl_1625_ = lean_ctor_get(v_code_1619_, 0);
                        v_k_1626_ = lean_ctor_get(v_code_1619_, 1);
                        lean_inc_ref(v_k_1626_);
                        v___x_1627_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_1626_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
                        if lean_obj_tag(v___x_1627_) == 0 {
                            v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
                            v_isSharedCheck_1650_ = (!lean_is_exclusive(v___x_1627_)) as u8;
                            if v_isSharedCheck_1650_ == 0 {
                                v___x_1630_ = v___x_1627_;
                                v_isShared_1631_ = v_isSharedCheck_1650_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1628_);
                                lean_dec(v___x_1627_);
                                v___x_1630_ = lean_box(0);
                                v_isShared_1631_ = v_isSharedCheck_1650_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_code_1619_, 2);
                            return v___x_1627_;
                        }
                    }
                    2 => {
                        v_decl_1651_ = lean_ctor_get(v_code_1619_, 0);
                        v_k_1652_ = lean_ctor_get(v_code_1619_, 1);
                        v_params_1653_ = lean_ctor_get(v_decl_1651_, 2);
                        v_type_1654_ = lean_ctor_get(v_decl_1651_, 3);
                        v_value_1655_ = lean_ctor_get(v_decl_1651_, 4);
                        lean_inc_ref(v_value_1655_);
                        v___x_1656_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_value_1655_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
                        if lean_obj_tag(v___x_1656_) == 0 {
                            v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
                            lean_inc(v_a_1657_);
                            lean_dec_ref_known(v___x_1656_, 1);
                            v___x_1658_ = 1;
                            lean_inc_ref(v_params_1653_);
                            lean_inc_ref(v_type_1654_);
                            lean_inc_ref(v_decl_1651_);
                            v___x_1659_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1658_, v_decl_1651_, v_type_1654_, v_params_1653_, v_a_1657_, v_a_1621_);
                            if lean_obj_tag(v___x_1659_) == 0 {
                                v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
                                lean_inc(v_a_1660_);
                                lean_dec_ref_known(v___x_1659_, 1);
                                lean_inc_ref(v_k_1652_);
                                v___x_1661_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_1652_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
                                if lean_obj_tag(v___x_1661_) == 0 {
                                    v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
                                    v_isSharedCheck_1689_ = (!lean_is_exclusive(v___x_1661_)) as u8;
                                    if v_isSharedCheck_1689_ == 0 {
                                        v___x_1664_ = v___x_1661_;
                                        v_isShared_1665_ = v_isSharedCheck_1689_;
                                        state = 6;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1662_);
                                        lean_dec(v___x_1661_);
                                        v___x_1664_ = lean_box(0);
                                        v_isShared_1665_ = v_isSharedCheck_1689_;
                                        state = 6;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_1660_);
                                    lean_dec_ref_known(v_code_1619_, 2);
                                    return v___x_1661_;
                                }
                            } else {
                                lean_dec_ref_known(v_code_1619_, 2);
                                v_a_1690_ = lean_ctor_get(v___x_1659_, 0);
                                v_isSharedCheck_1697_ = (!lean_is_exclusive(v___x_1659_)) as u8;
                                if v_isSharedCheck_1697_ == 0 {
                                    v___x_1692_ = v___x_1659_;
                                    v_isShared_1693_ = v_isSharedCheck_1697_;
                                    state = 12;
                                    continue;
                                } else {
                                    lean_inc(v_a_1690_);
                                    lean_dec(v___x_1659_);
                                    v___x_1692_ = lean_box(0);
                                    v_isShared_1693_ = v_isSharedCheck_1697_;
                                    state = 12;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref_known(v_code_1619_, 2);
                            return v___x_1656_;
                        }
                    }
                    4 => {
                        v_cases_1698_ = lean_ctor_get(v_code_1619_, 0);
                        lean_inc_ref(v_cases_1698_);
                        lean_dec_ref_known(v_code_1619_, 1);
                        v_typeName_1699_ = lean_ctor_get(v_cases_1698_, 0);
                        v_resultType_1700_ = lean_ctor_get(v_cases_1698_, 1);
                        v_discr_1701_ = lean_ctor_get(v_cases_1698_, 2);
                        v_alts_1702_ = lean_ctor_get(v_cases_1698_, 3);
                        v_isSharedCheck_1721_ = (!lean_is_exclusive(v_cases_1698_)) as u8;
                        if v_isSharedCheck_1721_ == 0 {
                            v___x_1704_ = v_cases_1698_;
                            v_isShared_1705_ = v_isSharedCheck_1721_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_alts_1702_);
                            lean_inc(v_discr_1701_);
                            lean_inc(v_resultType_1700_);
                            lean_inc(v_typeName_1699_);
                            lean_dec(v_cases_1698_);
                            v___x_1704_ = lean_box(0);
                            v_isShared_1705_ = v_isSharedCheck_1721_;
                            state = 14;
                            continue;
                        }
                    }
                    7 => {
                        v_fvarId_1722_ = lean_ctor_get(v_code_1619_, 0);
                        v_i_1723_ = lean_ctor_get(v_code_1619_, 1);
                        v_y_1724_ = lean_ctor_get(v_code_1619_, 2);
                        v_k_1725_ = lean_ctor_get(v_code_1619_, 3);
                        lean_inc_ref(v_k_1725_);
                        v___x_1726_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_1725_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
                        if lean_obj_tag(v___x_1726_) == 0 {
                            v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
                            v_isSharedCheck_1751_ = (!lean_is_exclusive(v___x_1726_)) as u8;
                            if v_isSharedCheck_1751_ == 0 {
                                v___x_1729_ = v___x_1726_;
                                v_isShared_1730_ = v_isSharedCheck_1751_;
                                state = 18;
                                continue;
                            } else {
                                lean_inc(v_a_1727_);
                                lean_dec(v___x_1726_);
                                v___x_1729_ = lean_box(0);
                                v_isShared_1730_ = v_isSharedCheck_1751_;
                                state = 18;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_code_1619_, 4);
                            return v___x_1726_;
                        }
                    }
                    8 => {
                        v_fvarId_1752_ = lean_ctor_get(v_code_1619_, 0);
                        v_i_1753_ = lean_ctor_get(v_code_1619_, 1);
                        v_y_1754_ = lean_ctor_get(v_code_1619_, 2);
                        v_k_1755_ = lean_ctor_get(v_code_1619_, 3);
                        lean_inc_ref(v_k_1755_);
                        v___x_1756_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_1755_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
                        if lean_obj_tag(v___x_1756_) == 0 {
                            v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
                            v_isSharedCheck_1781_ = (!lean_is_exclusive(v___x_1756_)) as u8;
                            if v_isSharedCheck_1781_ == 0 {
                                v___x_1759_ = v___x_1756_;
                                v_isShared_1760_ = v_isSharedCheck_1781_;
                                state = 23;
                                continue;
                            } else {
                                lean_inc(v_a_1757_);
                                lean_dec(v___x_1756_);
                                v___x_1759_ = lean_box(0);
                                v_isShared_1760_ = v_isSharedCheck_1781_;
                                state = 23;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_code_1619_, 4);
                            return v___x_1756_;
                        }
                    }
                    9 => {
                        v_fvarId_1782_ = lean_ctor_get(v_code_1619_, 0);
                        v_i_1783_ = lean_ctor_get(v_code_1619_, 1);
                        v_offset_1784_ = lean_ctor_get(v_code_1619_, 2);
                        v_y_1785_ = lean_ctor_get(v_code_1619_, 3);
                        v_ty_1786_ = lean_ctor_get(v_code_1619_, 4);
                        v_k_1787_ = lean_ctor_get(v_code_1619_, 5);
                        lean_inc_ref(v_k_1787_);
                        v___x_1788_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_1787_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
                        if lean_obj_tag(v___x_1788_) == 0 {
                            v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
                            v_isSharedCheck_1815_ = (!lean_is_exclusive(v___x_1788_)) as u8;
                            if v_isSharedCheck_1815_ == 0 {
                                v___x_1791_ = v___x_1788_;
                                v_isShared_1792_ = v_isSharedCheck_1815_;
                                state = 28;
                                continue;
                            } else {
                                lean_inc(v_a_1789_);
                                lean_dec(v___x_1788_);
                                v___x_1791_ = lean_box(0);
                                v_isShared_1792_ = v_isSharedCheck_1815_;
                                state = 28;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_code_1619_, 6);
                            return v___x_1788_;
                        }
                    }
                    10 => {
                        v_fvarId_1816_ = lean_ctor_get(v_code_1619_, 0);
                        v_cidx_1817_ = lean_ctor_get(v_code_1619_, 1);
                        v_k_1818_ = lean_ctor_get(v_code_1619_, 2);
                        lean_inc_ref(v_k_1818_);
                        v___x_1819_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_1818_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
                        if lean_obj_tag(v___x_1819_) == 0 {
                            v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
                            v_isSharedCheck_1843_ = (!lean_is_exclusive(v___x_1819_)) as u8;
                            if v_isSharedCheck_1843_ == 0 {
                                v___x_1822_ = v___x_1819_;
                                v_isShared_1823_ = v_isSharedCheck_1843_;
                                state = 33;
                                continue;
                            } else {
                                lean_inc(v_a_1820_);
                                lean_dec(v___x_1819_);
                                v___x_1822_ = lean_box(0);
                                v_isShared_1823_ = v_isSharedCheck_1843_;
                                state = 33;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_code_1619_, 3);
                            return v___x_1819_;
                        }
                    }
                    11 => {
                        v_fvarId_1844_ = lean_ctor_get(v_code_1619_, 0);
                        v_n_1845_ = lean_ctor_get(v_code_1619_, 1);
                        v_check_1846_ = lean_ctor_get_uint8(
                            v_code_1619_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        );
                        v_persistent_1847_ = lean_ctor_get_uint8(
                            v_code_1619_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        );
                        v_k_1848_ = lean_ctor_get(v_code_1619_, 2);
                        lean_inc_ref(v_k_1848_);
                        v___x_1849_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_1848_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
                        if lean_obj_tag(v___x_1849_) == 0 {
                            v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
                            v_isSharedCheck_1873_ = (!lean_is_exclusive(v___x_1849_)) as u8;
                            if v_isSharedCheck_1873_ == 0 {
                                v___x_1852_ = v___x_1849_;
                                v_isShared_1853_ = v_isSharedCheck_1873_;
                                state = 38;
                                continue;
                            } else {
                                lean_inc(v_a_1850_);
                                lean_dec(v___x_1849_);
                                v___x_1852_ = lean_box(0);
                                v_isShared_1853_ = v_isSharedCheck_1873_;
                                state = 38;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_code_1619_, 3);
                            return v___x_1849_;
                        }
                    }
                    12 => {
                        v_fvarId_1874_ = lean_ctor_get(v_code_1619_, 0);
                        v_n_1875_ = lean_ctor_get(v_code_1619_, 1);
                        v_check_1876_ = lean_ctor_get_uint8(
                            v_code_1619_,
                            (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        );
                        v_persistent_1877_ = lean_ctor_get_uint8(
                            v_code_1619_,
                            (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                        );
                        v_objs_x3f_1878_ = lean_ctor_get(v_code_1619_, 2);
                        v_k_1879_ = lean_ctor_get(v_code_1619_, 3);
                        lean_inc_ref(v_k_1879_);
                        v___x_1880_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_1879_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
                        if lean_obj_tag(v___x_1880_) == 0 {
                            v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
                            v_isSharedCheck_1905_ = (!lean_is_exclusive(v___x_1880_)) as u8;
                            if v_isSharedCheck_1905_ == 0 {
                                v___x_1883_ = v___x_1880_;
                                v_isShared_1884_ = v_isSharedCheck_1905_;
                                state = 43;
                                continue;
                            } else {
                                lean_inc(v_a_1881_);
                                lean_dec(v___x_1880_);
                                v___x_1883_ = lean_box(0);
                                v_isShared_1884_ = v_isSharedCheck_1905_;
                                state = 43;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_code_1619_, 4);
                            return v___x_1880_;
                        }
                    }
                    13 => {
                        v_fvarId_1906_ = lean_ctor_get(v_code_1619_, 0);
                        v_k_1907_ = lean_ctor_get(v_code_1619_, 1);
                        lean_inc_ref(v_k_1907_);
                        v___x_1908_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_1907_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
                        if lean_obj_tag(v___x_1908_) == 0 {
                            v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
                            v_isSharedCheck_1931_ = (!lean_is_exclusive(v___x_1908_)) as u8;
                            if v_isSharedCheck_1931_ == 0 {
                                v___x_1911_ = v___x_1908_;
                                v_isShared_1912_ = v_isSharedCheck_1931_;
                                state = 48;
                                continue;
                            } else {
                                lean_inc(v_a_1909_);
                                lean_dec(v___x_1908_);
                                v___x_1911_ = lean_box(0);
                                v_isShared_1912_ = v_isSharedCheck_1931_;
                                state = 48;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_code_1619_, 2);
                            return v___x_1908_;
                        }
                    }
                    _ => {
                        v___x_1932_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1932_, 0, v_code_1619_);
                        return v___x_1932_;
                    }
                }
            }
            1 => {
                v___x_1632_ = lean_ptr_addr(v_k_1626_);
                v___x_1633_ = lean_ptr_addr(v_a_1628_);
                v___x_1634_ = lean_usize_dec_eq(v___x_1632_, v___x_1633_);
                if v___x_1634_ == 0 {
                    lean_inc_ref(v_decl_1625_);
                    v_isSharedCheck_1644_ = (!lean_is_exclusive(v_code_1619_)) as u8;
                    if v_isSharedCheck_1644_ == 0 {
                        v_unused_1645_ = lean_ctor_get(v_code_1619_, 1);
                        lean_dec(v_unused_1645_);
                        v_unused_1646_ = lean_ctor_get(v_code_1619_, 0);
                        lean_dec(v_unused_1646_);
                        v___x_1636_ = v_code_1619_;
                        v_isShared_1637_ = v_isSharedCheck_1644_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_code_1619_);
                        v___x_1636_ = lean_box(0);
                        v_isShared_1637_ = v_isSharedCheck_1644_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1628_);
                    if v_isShared_1631_ == 0 {
                        lean_ctor_set(v___x_1630_, 0, v_code_1619_);
                        v___x_1648_ = v___x_1630_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_code_1619_);
                        v___x_1648_ = v_reuseFailAlloc_1649_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1637_ == 0 {
                    lean_ctor_set(v___x_1636_, 1, v_a_1628_);
                    v___x_1639_ = v___x_1636_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_decl_1625_);
                    lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_a_1628_);
                    v___x_1639_ = v_reuseFailAlloc_1643_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1631_ == 0 {
                    lean_ctor_set(v___x_1630_, 0, v___x_1639_);
                    v___x_1641_ = v___x_1630_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
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
                    v_isSharedCheck_1677_ = (!lean_is_exclusive(v_code_1619_)) as u8;
                    if v_isSharedCheck_1677_ == 0 {
                        v_unused_1678_ = lean_ctor_get(v_code_1619_, 1);
                        lean_dec(v_unused_1678_);
                        v_unused_1679_ = lean_ctor_get(v_code_1619_, 0);
                        lean_dec(v_unused_1679_);
                        v___x_1669_ = v_code_1619_;
                        v_isShared_1670_ = v_isSharedCheck_1677_;
                        state = 8;
                        continue;
                    } else {
                        lean_dec(v_code_1619_);
                        v___x_1669_ = lean_box(0);
                        v_isShared_1670_ = v_isSharedCheck_1677_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1662_);
                    lean_dec(v_a_1660_);
                    if v_isShared_1665_ == 0 {
                        lean_ctor_set(v___x_1664_, 0, v_code_1619_);
                        v___x_1681_ = v___x_1664_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_code_1619_);
                        v___x_1681_ = v_reuseFailAlloc_1682_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_1670_ == 0 {
                    lean_ctor_set(v___x_1669_, 1, v_a_1662_);
                    lean_ctor_set(v___x_1669_, 0, v_a_1660_);
                    v___x_1672_ = v___x_1669_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1676_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1660_);
                    lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_a_1662_);
                    v___x_1672_ = v_reuseFailAlloc_1676_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_1665_ == 0 {
                    lean_ctor_set(v___x_1664_, 0, v___x_1672_);
                    v___x_1674_ = v___x_1664_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1672_);
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
                    v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
                    v___x_1695_ = v_reuseFailAlloc_1696_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1695_;
            }
            14 => {
                v___x_1706_ = lean_unsigned_to_nat(0);
                v___x_1707_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1(v___x_1706_, v_alts_1702_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
                if lean_obj_tag(v___x_1707_) == 0 {
                    v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
                    lean_inc(v_a_1708_);
                    lean_dec_ref_known(v___x_1707_, 1);
                    if v_isShared_1705_ == 0 {
                        lean_ctor_set(v___x_1704_, 3, v_a_1708_);
                        v___x_1710_ = v___x_1704_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 4, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_typeName_1699_);
                        lean_ctor_set(v_reuseFailAlloc_1712_, 1, v_resultType_1700_);
                        lean_ctor_set(v_reuseFailAlloc_1712_, 2, v_discr_1701_);
                        lean_ctor_set(v_reuseFailAlloc_1712_, 3, v_a_1708_);
                        v___x_1710_ = v_reuseFailAlloc_1712_;
                        state = 15;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1704_);
                    lean_dec(v_discr_1701_);
                    lean_dec_ref(v_resultType_1700_);
                    lean_dec(v_typeName_1699_);
                    v_a_1713_ = lean_ctor_get(v___x_1707_, 0);
                    v_isSharedCheck_1720_ = (!lean_is_exclusive(v___x_1707_)) as u8;
                    if v_isSharedCheck_1720_ == 0 {
                        v___x_1715_ = v___x_1707_;
                        v_isShared_1716_ = v_isSharedCheck_1720_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_1713_);
                        lean_dec(v___x_1707_);
                        v___x_1715_ = lean_box(0);
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
                    v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
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
                    lean_inc(v_y_1724_);
                    lean_inc(v_i_1723_);
                    lean_inc(v_fvarId_1722_);
                    v_isSharedCheck_1743_ = (!lean_is_exclusive(v_code_1619_)) as u8;
                    if v_isSharedCheck_1743_ == 0 {
                        v_unused_1744_ = lean_ctor_get(v_code_1619_, 3);
                        lean_dec(v_unused_1744_);
                        v_unused_1745_ = lean_ctor_get(v_code_1619_, 2);
                        lean_dec(v_unused_1745_);
                        v_unused_1746_ = lean_ctor_get(v_code_1619_, 1);
                        lean_dec(v_unused_1746_);
                        v_unused_1747_ = lean_ctor_get(v_code_1619_, 0);
                        lean_dec(v_unused_1747_);
                        v___x_1735_ = v_code_1619_;
                        v_isShared_1736_ = v_isSharedCheck_1743_;
                        state = 19;
                        continue;
                    } else {
                        lean_dec(v_code_1619_);
                        v___x_1735_ = lean_box(0);
                        v_isShared_1736_ = v_isSharedCheck_1743_;
                        state = 19;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1727_);
                    if v_isShared_1730_ == 0 {
                        lean_ctor_set(v___x_1729_, 0, v_code_1619_);
                        v___x_1749_ = v___x_1729_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_code_1619_);
                        v___x_1749_ = v_reuseFailAlloc_1750_;
                        state = 22;
                        continue;
                    }
                }
            }
            19 => {
                if v_isShared_1736_ == 0 {
                    lean_ctor_set(v___x_1735_, 3, v_a_1727_);
                    v___x_1738_ = v___x_1735_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1742_ = lean_alloc_ctor(7, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_fvarId_1722_);
                    lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_i_1723_);
                    lean_ctor_set(v_reuseFailAlloc_1742_, 2, v_y_1724_);
                    lean_ctor_set(v_reuseFailAlloc_1742_, 3, v_a_1727_);
                    v___x_1738_ = v_reuseFailAlloc_1742_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_1730_ == 0 {
                    lean_ctor_set(v___x_1729_, 0, v___x_1738_);
                    v___x_1740_ = v___x_1729_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1738_);
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
                    lean_inc(v_y_1754_);
                    lean_inc(v_i_1753_);
                    lean_inc(v_fvarId_1752_);
                    v_isSharedCheck_1773_ = (!lean_is_exclusive(v_code_1619_)) as u8;
                    if v_isSharedCheck_1773_ == 0 {
                        v_unused_1774_ = lean_ctor_get(v_code_1619_, 3);
                        lean_dec(v_unused_1774_);
                        v_unused_1775_ = lean_ctor_get(v_code_1619_, 2);
                        lean_dec(v_unused_1775_);
                        v_unused_1776_ = lean_ctor_get(v_code_1619_, 1);
                        lean_dec(v_unused_1776_);
                        v_unused_1777_ = lean_ctor_get(v_code_1619_, 0);
                        lean_dec(v_unused_1777_);
                        v___x_1765_ = v_code_1619_;
                        v_isShared_1766_ = v_isSharedCheck_1773_;
                        state = 24;
                        continue;
                    } else {
                        lean_dec(v_code_1619_);
                        v___x_1765_ = lean_box(0);
                        v_isShared_1766_ = v_isSharedCheck_1773_;
                        state = 24;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1757_);
                    if v_isShared_1760_ == 0 {
                        lean_ctor_set(v___x_1759_, 0, v_code_1619_);
                        v___x_1779_ = v___x_1759_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_code_1619_);
                        v___x_1779_ = v_reuseFailAlloc_1780_;
                        state = 27;
                        continue;
                    }
                }
            }
            24 => {
                if v_isShared_1766_ == 0 {
                    lean_ctor_set(v___x_1765_, 3, v_a_1757_);
                    v___x_1768_ = v___x_1765_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_1772_ = lean_alloc_ctor(8, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_fvarId_1752_);
                    lean_ctor_set(v_reuseFailAlloc_1772_, 1, v_i_1753_);
                    lean_ctor_set(v_reuseFailAlloc_1772_, 2, v_y_1754_);
                    lean_ctor_set(v_reuseFailAlloc_1772_, 3, v_a_1757_);
                    v___x_1768_ = v_reuseFailAlloc_1772_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                if v_isShared_1760_ == 0 {
                    lean_ctor_set(v___x_1759_, 0, v___x_1768_);
                    v___x_1770_ = v___x_1759_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1768_);
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
                    lean_inc_ref(v_ty_1786_);
                    lean_inc(v_y_1785_);
                    lean_inc(v_offset_1784_);
                    lean_inc(v_i_1783_);
                    lean_inc(v_fvarId_1782_);
                    v_isSharedCheck_1805_ = (!lean_is_exclusive(v_code_1619_)) as u8;
                    if v_isSharedCheck_1805_ == 0 {
                        v_unused_1806_ = lean_ctor_get(v_code_1619_, 5);
                        lean_dec(v_unused_1806_);
                        v_unused_1807_ = lean_ctor_get(v_code_1619_, 4);
                        lean_dec(v_unused_1807_);
                        v_unused_1808_ = lean_ctor_get(v_code_1619_, 3);
                        lean_dec(v_unused_1808_);
                        v_unused_1809_ = lean_ctor_get(v_code_1619_, 2);
                        lean_dec(v_unused_1809_);
                        v_unused_1810_ = lean_ctor_get(v_code_1619_, 1);
                        lean_dec(v_unused_1810_);
                        v_unused_1811_ = lean_ctor_get(v_code_1619_, 0);
                        lean_dec(v_unused_1811_);
                        v___x_1797_ = v_code_1619_;
                        v_isShared_1798_ = v_isSharedCheck_1805_;
                        state = 29;
                        continue;
                    } else {
                        lean_dec(v_code_1619_);
                        v___x_1797_ = lean_box(0);
                        v_isShared_1798_ = v_isSharedCheck_1805_;
                        state = 29;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1789_);
                    if v_isShared_1792_ == 0 {
                        lean_ctor_set(v___x_1791_, 0, v_code_1619_);
                        v___x_1813_ = v___x_1791_;
                        state = 32;
                        continue;
                    } else {
                        v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_code_1619_);
                        v___x_1813_ = v_reuseFailAlloc_1814_;
                        state = 32;
                        continue;
                    }
                }
            }
            29 => {
                if v_isShared_1798_ == 0 {
                    lean_ctor_set(v___x_1797_, 5, v_a_1789_);
                    v___x_1800_ = v___x_1797_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1804_ = lean_alloc_ctor(9, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_fvarId_1782_);
                    lean_ctor_set(v_reuseFailAlloc_1804_, 1, v_i_1783_);
                    lean_ctor_set(v_reuseFailAlloc_1804_, 2, v_offset_1784_);
                    lean_ctor_set(v_reuseFailAlloc_1804_, 3, v_y_1785_);
                    lean_ctor_set(v_reuseFailAlloc_1804_, 4, v_ty_1786_);
                    lean_ctor_set(v_reuseFailAlloc_1804_, 5, v_a_1789_);
                    v___x_1800_ = v_reuseFailAlloc_1804_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                if v_isShared_1792_ == 0 {
                    lean_ctor_set(v___x_1791_, 0, v___x_1800_);
                    v___x_1802_ = v___x_1791_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1800_);
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
                    lean_inc(v_cidx_1817_);
                    lean_inc(v_fvarId_1816_);
                    v_isSharedCheck_1836_ = (!lean_is_exclusive(v_code_1619_)) as u8;
                    if v_isSharedCheck_1836_ == 0 {
                        v_unused_1837_ = lean_ctor_get(v_code_1619_, 2);
                        lean_dec(v_unused_1837_);
                        v_unused_1838_ = lean_ctor_get(v_code_1619_, 1);
                        lean_dec(v_unused_1838_);
                        v_unused_1839_ = lean_ctor_get(v_code_1619_, 0);
                        lean_dec(v_unused_1839_);
                        v___x_1828_ = v_code_1619_;
                        v_isShared_1829_ = v_isSharedCheck_1836_;
                        state = 34;
                        continue;
                    } else {
                        lean_dec(v_code_1619_);
                        v___x_1828_ = lean_box(0);
                        v_isShared_1829_ = v_isSharedCheck_1836_;
                        state = 34;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1820_);
                    if v_isShared_1823_ == 0 {
                        lean_ctor_set(v___x_1822_, 0, v_code_1619_);
                        v___x_1841_ = v___x_1822_;
                        state = 37;
                        continue;
                    } else {
                        v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_code_1619_);
                        v___x_1841_ = v_reuseFailAlloc_1842_;
                        state = 37;
                        continue;
                    }
                }
            }
            34 => {
                if v_isShared_1829_ == 0 {
                    lean_ctor_set(v___x_1828_, 2, v_a_1820_);
                    v___x_1831_ = v___x_1828_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_1835_ = lean_alloc_ctor(10, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_fvarId_1816_);
                    lean_ctor_set(v_reuseFailAlloc_1835_, 1, v_cidx_1817_);
                    lean_ctor_set(v_reuseFailAlloc_1835_, 2, v_a_1820_);
                    v___x_1831_ = v_reuseFailAlloc_1835_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_1823_ == 0 {
                    lean_ctor_set(v___x_1822_, 0, v___x_1831_);
                    v___x_1833_ = v___x_1822_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1831_);
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
                    lean_inc(v_n_1845_);
                    lean_inc(v_fvarId_1844_);
                    v_isSharedCheck_1866_ = (!lean_is_exclusive(v_code_1619_)) as u8;
                    if v_isSharedCheck_1866_ == 0 {
                        v_unused_1867_ = lean_ctor_get(v_code_1619_, 2);
                        lean_dec(v_unused_1867_);
                        v_unused_1868_ = lean_ctor_get(v_code_1619_, 1);
                        lean_dec(v_unused_1868_);
                        v_unused_1869_ = lean_ctor_get(v_code_1619_, 0);
                        lean_dec(v_unused_1869_);
                        v___x_1858_ = v_code_1619_;
                        v_isShared_1859_ = v_isSharedCheck_1866_;
                        state = 39;
                        continue;
                    } else {
                        lean_dec(v_code_1619_);
                        v___x_1858_ = lean_box(0);
                        v_isShared_1859_ = v_isSharedCheck_1866_;
                        state = 39;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1850_);
                    if v_isShared_1853_ == 0 {
                        lean_ctor_set(v___x_1852_, 0, v_code_1619_);
                        v___x_1871_ = v___x_1852_;
                        state = 42;
                        continue;
                    } else {
                        v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_code_1619_);
                        v___x_1871_ = v_reuseFailAlloc_1872_;
                        state = 42;
                        continue;
                    }
                }
            }
            39 => {
                if v_isShared_1859_ == 0 {
                    lean_ctor_set(v___x_1858_, 2, v_a_1850_);
                    v___x_1861_ = v___x_1858_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_1865_ = lean_alloc_ctor(11, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_fvarId_1844_);
                    lean_ctor_set(v_reuseFailAlloc_1865_, 1, v_n_1845_);
                    lean_ctor_set(v_reuseFailAlloc_1865_, 2, v_a_1850_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1865_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_check_1846_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1865_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_persistent_1847_,
                    );
                    v___x_1861_ = v_reuseFailAlloc_1865_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_1853_ == 0 {
                    lean_ctor_set(v___x_1852_, 0, v___x_1861_);
                    v___x_1863_ = v___x_1852_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1861_);
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
                    lean_inc(v_objs_x3f_1878_);
                    lean_inc(v_n_1875_);
                    lean_inc(v_fvarId_1874_);
                    v_isSharedCheck_1897_ = (!lean_is_exclusive(v_code_1619_)) as u8;
                    if v_isSharedCheck_1897_ == 0 {
                        v_unused_1898_ = lean_ctor_get(v_code_1619_, 3);
                        lean_dec(v_unused_1898_);
                        v_unused_1899_ = lean_ctor_get(v_code_1619_, 2);
                        lean_dec(v_unused_1899_);
                        v_unused_1900_ = lean_ctor_get(v_code_1619_, 1);
                        lean_dec(v_unused_1900_);
                        v_unused_1901_ = lean_ctor_get(v_code_1619_, 0);
                        lean_dec(v_unused_1901_);
                        v___x_1889_ = v_code_1619_;
                        v_isShared_1890_ = v_isSharedCheck_1897_;
                        state = 44;
                        continue;
                    } else {
                        lean_dec(v_code_1619_);
                        v___x_1889_ = lean_box(0);
                        v_isShared_1890_ = v_isSharedCheck_1897_;
                        state = 44;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1881_);
                    if v_isShared_1884_ == 0 {
                        lean_ctor_set(v___x_1883_, 0, v_code_1619_);
                        v___x_1903_ = v___x_1883_;
                        state = 47;
                        continue;
                    } else {
                        v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_code_1619_);
                        v___x_1903_ = v_reuseFailAlloc_1904_;
                        state = 47;
                        continue;
                    }
                }
            }
            44 => {
                if v_isShared_1890_ == 0 {
                    lean_ctor_set(v___x_1889_, 3, v_a_1881_);
                    v___x_1892_ = v___x_1889_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_1896_ = lean_alloc_ctor(12, 4, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_fvarId_1874_);
                    lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_n_1875_);
                    lean_ctor_set(v_reuseFailAlloc_1896_, 2, v_objs_x3f_1878_);
                    lean_ctor_set(v_reuseFailAlloc_1896_, 3, v_a_1881_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1896_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_check_1876_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1896_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                        v_persistent_1877_,
                    );
                    v___x_1892_ = v_reuseFailAlloc_1896_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_1884_ == 0 {
                    lean_ctor_set(v___x_1883_, 0, v___x_1892_);
                    v___x_1894_ = v___x_1883_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1892_);
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
                    lean_inc(v_fvarId_1906_);
                    v_isSharedCheck_1925_ = (!lean_is_exclusive(v_code_1619_)) as u8;
                    if v_isSharedCheck_1925_ == 0 {
                        v_unused_1926_ = lean_ctor_get(v_code_1619_, 1);
                        lean_dec(v_unused_1926_);
                        v_unused_1927_ = lean_ctor_get(v_code_1619_, 0);
                        lean_dec(v_unused_1927_);
                        v___x_1917_ = v_code_1619_;
                        v_isShared_1918_ = v_isSharedCheck_1925_;
                        state = 49;
                        continue;
                    } else {
                        lean_dec(v_code_1619_);
                        v___x_1917_ = lean_box(0);
                        v_isShared_1918_ = v_isSharedCheck_1925_;
                        state = 49;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1909_);
                    if v_isShared_1912_ == 0 {
                        lean_ctor_set(v___x_1911_, 0, v_code_1619_);
                        v___x_1929_ = v___x_1911_;
                        state = 52;
                        continue;
                    } else {
                        v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_code_1619_);
                        v___x_1929_ = v_reuseFailAlloc_1930_;
                        state = 52;
                        continue;
                    }
                }
            }
            49 => {
                if v_isShared_1918_ == 0 {
                    lean_ctor_set(v___x_1917_, 1, v_a_1909_);
                    v___x_1920_ = v___x_1917_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_1924_ = lean_alloc_ctor(13, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_fvarId_1906_);
                    lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_a_1909_);
                    v___x_1920_ = v_reuseFailAlloc_1924_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                if v_isShared_1912_ == 0 {
                    lean_ctor_set(v___x_1911_, 0, v___x_1920_);
                    v___x_1922_ = v___x_1911_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1920_);
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
    mut v_code_1933_: *mut LeanObject,
    mut v_a_1934_: *mut LeanObject,
    mut v_a_1935_: *mut LeanObject,
    mut v_a_1936_: *mut LeanObject,
    mut v_a_1937_: *mut LeanObject,
    mut v_a_1938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1939_: *mut LeanObject = core::ptr::null_mut();
    v_res_1939_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(
        v_code_1933_,
        v_a_1934_,
        v_a_1935_,
        v_a_1936_,
        v_a_1937_,
    );
    lean_dec(v_a_1937_);
    lean_dec_ref(v_a_1936_);
    lean_dec(v_a_1935_);
    lean_dec_ref(v_a_1934_);
    return v_res_1939_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1(
    mut v_i_1940_: *mut LeanObject,
    mut v_as_1941_: *mut LeanObject,
    mut v___y_1942_: *mut LeanObject,
    mut v___y_1943_: *mut LeanObject,
    mut v___y_1944_: *mut LeanObject,
    mut v___y_1945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: u8 = 0;
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: usize = 0;
    let mut v___x_1955_: usize = 0;
    let mut v___x_1956_: u8 = 0;
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1967_: u8 = 0;
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1971_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1947_ = lean_array_get_size(v_as_1941_);
                v___x_1948_ = lean_nat_dec_lt(v_i_1940_, v___x_1947_);
                if v___x_1948_ == 0 {
                    lean_dec(v_i_1940_);
                    v___x_1949_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1949_, 0, v_as_1941_);
                    return v___x_1949_;
                } else {
                    v___f_1950_ = lean_alloc_closure(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase___boxed as *mut core::ffi::c_void, 6, 0);
                    v_a_1951_ = lean_array_fget_borrowed(v_as_1941_, v_i_1940_);
                    lean_inc(v_a_1951_);
                    v___x_1952_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg(v_a_1951_, v___f_1950_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
                    if lean_obj_tag(v___x_1952_) == 0 {
                        v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
                        lean_inc(v_a_1953_);
                        lean_dec_ref_known(v___x_1952_, 1);
                        v___x_1954_ = lean_ptr_addr(v_a_1951_);
                        v___x_1955_ = lean_ptr_addr(v_a_1953_);
                        v___x_1956_ = lean_usize_dec_eq(v___x_1954_, v___x_1955_);
                        if v___x_1956_ == 0 {
                            v___x_1957_ = lean_unsigned_to_nat(1);
                            v___x_1958_ = lean_nat_add(v_i_1940_, v___x_1957_);
                            v___x_1959_ = lean_array_fset(v_as_1941_, v_i_1940_, v_a_1953_);
                            lean_dec(v_i_1940_);
                            v_i_1940_ = v___x_1958_;
                            v_as_1941_ = v___x_1959_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_a_1953_);
                            v___x_1961_ = lean_unsigned_to_nat(1);
                            v___x_1962_ = lean_nat_add(v_i_1940_, v___x_1961_);
                            lean_dec(v_i_1940_);
                            v_i_1940_ = v___x_1962_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_as_1941_);
                        lean_dec(v_i_1940_);
                        v_a_1964_ = lean_ctor_get(v___x_1952_, 0);
                        v_isSharedCheck_1971_ = (!lean_is_exclusive(v___x_1952_)) as u8;
                        if v_isSharedCheck_1971_ == 0 {
                            v___x_1966_ = v___x_1952_;
                            v_isShared_1967_ = v_isSharedCheck_1971_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1964_);
                            lean_dec(v___x_1952_);
                            v___x_1966_ = lean_box(0);
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
                    v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
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
    mut v_i_1972_: *mut LeanObject,
    mut v_as_1973_: *mut LeanObject,
    mut v___y_1974_: *mut LeanObject,
    mut v___y_1975_: *mut LeanObject,
    mut v___y_1976_: *mut LeanObject,
    mut v___y_1977_: *mut LeanObject,
    mut v___y_1978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1979_: *mut LeanObject = core::ptr::null_mut();
    v_res_1979_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1(v_i_1972_, v_as_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
    lean_dec(v___y_1977_);
    lean_dec_ref(v___y_1976_);
    lean_dec(v___y_1975_);
    lean_dec_ref(v___y_1974_);
    return v_res_1979_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg(
    mut v_f_1980_: *mut LeanObject,
    mut v_v_1981_: *mut LeanObject,
    mut v___y_1982_: *mut LeanObject,
    mut v___y_1983_: *mut LeanObject,
    mut v___y_1984_: *mut LeanObject,
    mut v___y_1985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_code_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1990_: u8 = 0;
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1995_: u8 = 0;
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2002_: u8 = 0;
    let mut v_a_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2006_: u8 = 0;
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2010_: u8 = 0;
    let mut v_isSharedCheck_2011_: u8 = 0;
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_1981_) == 0 {
                    v_code_1987_ = lean_ctor_get(v_v_1981_, 0);
                    v_isSharedCheck_2011_ = (!lean_is_exclusive(v_v_1981_)) as u8;
                    if v_isSharedCheck_2011_ == 0 {
                        v___x_1989_ = v_v_1981_;
                        v_isShared_1990_ = v_isSharedCheck_2011_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_code_1987_);
                        lean_dec(v_v_1981_);
                        v___x_1989_ = lean_box(0);
                        v_isShared_1990_ = v_isSharedCheck_2011_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_f_1980_);
                    v___x_2012_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2012_, 0, v_v_1981_);
                    return v___x_2012_;
                }
            }
            1 => {
                lean_inc(v___y_1985_);
                lean_inc_ref(v___y_1984_);
                lean_inc(v___y_1983_);
                lean_inc_ref(v___y_1982_);
                v___x_1991_ = lean_apply_6(
                    v_f_1980_,
                    v_code_1987_,
                    v___y_1982_,
                    v___y_1983_,
                    v___y_1984_,
                    v___y_1985_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1991_) == 0 {
                    v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
                    v_isSharedCheck_2002_ = (!lean_is_exclusive(v___x_1991_)) as u8;
                    if v_isSharedCheck_2002_ == 0 {
                        v___x_1994_ = v___x_1991_;
                        v_isShared_1995_ = v_isSharedCheck_2002_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1992_);
                        lean_dec(v___x_1991_);
                        v___x_1994_ = lean_box(0);
                        v_isShared_1995_ = v_isSharedCheck_2002_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1989_);
                    v_a_2003_ = lean_ctor_get(v___x_1991_, 0);
                    v_isSharedCheck_2010_ = (!lean_is_exclusive(v___x_1991_)) as u8;
                    if v_isSharedCheck_2010_ == 0 {
                        v___x_2005_ = v___x_1991_;
                        v_isShared_2006_ = v_isSharedCheck_2010_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2003_);
                        lean_dec(v___x_1991_);
                        v___x_2005_ = lean_box(0);
                        v_isShared_2006_ = v_isSharedCheck_2010_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1990_ == 0 {
                    lean_ctor_set(v___x_1989_, 0, v_a_1992_);
                    v___x_1997_ = v___x_1989_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1992_);
                    v___x_1997_ = v_reuseFailAlloc_2001_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1995_ == 0 {
                    lean_ctor_set(v___x_1994_, 0, v___x_1997_);
                    v___x_1999_ = v___x_1994_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1997_);
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
                    v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2003_);
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
    mut v_f_2013_: *mut LeanObject,
    mut v_v_2014_: *mut LeanObject,
    mut v___y_2015_: *mut LeanObject,
    mut v___y_2016_: *mut LeanObject,
    mut v___y_2017_: *mut LeanObject,
    mut v___y_2018_: *mut LeanObject,
    mut v___y_2019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2020_: *mut LeanObject = core::ptr::null_mut();
    v_res_2020_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg(v_f_2013_, v_v_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
    lean_dec(v___y_2018_);
    lean_dec_ref(v___y_2017_);
    lean_dec(v___y_2016_);
    lean_dec_ref(v___y_2015_);
    return v_res_2020_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0(
    mut v_pu_2021_: u8,
    mut v_f_2022_: *mut LeanObject,
    mut v_v_2023_: *mut LeanObject,
    mut v___y_2024_: *mut LeanObject,
    mut v___y_2025_: *mut LeanObject,
    mut v___y_2026_: *mut LeanObject,
    mut v___y_2027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    v___x_2029_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg(v_f_2022_, v_v_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
    return v___x_2029_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___boxed(
    mut v_pu_2030_: *mut LeanObject,
    mut v_f_2031_: *mut LeanObject,
    mut v_v_2032_: *mut LeanObject,
    mut v___y_2033_: *mut LeanObject,
    mut v___y_2034_: *mut LeanObject,
    mut v___y_2035_: *mut LeanObject,
    mut v___y_2036_: *mut LeanObject,
    mut v___y_2037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_2038_: u8 = 0;
    let mut v_res_2039_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_2038_ = (lean_unbox(v_pu_2030_) as u8);
    v_res_2039_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0(v_pu_boxed_2038_, v_f_2031_, v_v_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
    lean_dec(v___y_2036_);
    lean_dec_ref(v___y_2035_);
    lean_dec(v___y_2034_);
    lean_dec_ref(v___y_2033_);
    return v_res_2039_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase(
    mut v_decl_2041_: *mut LeanObject,
    mut v_a_2042_: *mut LeanObject,
    mut v_a_2043_: *mut LeanObject,
    mut v_a_2044_: *mut LeanObject,
    mut v_a_2045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSignature_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recursive_2049_: u8 = 0;
    let mut v_inlineAttr_x3f_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2053_: u8 = 0;
    let mut v___f_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2059_: u8 = 0;
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2066_: u8 = 0;
    let mut v_a_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2070_: u8 = 0;
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2074_: u8 = 0;
    let mut v_isSharedCheck_2075_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSignature_2047_ = lean_ctor_get(v_decl_2041_, 0);
                v_value_2048_ = lean_ctor_get(v_decl_2041_, 1);
                v_recursive_2049_ = lean_ctor_get_uint8(
                    v_decl_2041_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_inlineAttr_x3f_2050_ = lean_ctor_get(v_decl_2041_, 2);
                v_isSharedCheck_2075_ = (!lean_is_exclusive(v_decl_2041_)) as u8;
                if v_isSharedCheck_2075_ == 0 {
                    v___x_2052_ = v_decl_2041_;
                    v_isShared_2053_ = v_isSharedCheck_2075_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_inlineAttr_x3f_2050_);
                    lean_inc(v_value_2048_);
                    lean_inc(v_toSignature_2047_);
                    lean_dec(v_decl_2041_);
                    v___x_2052_ = lean_box(0);
                    v_isShared_2053_ = v_isSharedCheck_2075_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_2054_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___closed__0;
                v___x_2055_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg(v___f_2054_, v_value_2048_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
                if lean_obj_tag(v___x_2055_) == 0 {
                    v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
                    v_isSharedCheck_2066_ = (!lean_is_exclusive(v___x_2055_)) as u8;
                    if v_isSharedCheck_2066_ == 0 {
                        v___x_2058_ = v___x_2055_;
                        v_isShared_2059_ = v_isSharedCheck_2066_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2056_);
                        lean_dec(v___x_2055_);
                        v___x_2058_ = lean_box(0);
                        v_isShared_2059_ = v_isSharedCheck_2066_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2052_);
                    lean_dec(v_inlineAttr_x3f_2050_);
                    lean_dec_ref(v_toSignature_2047_);
                    v_a_2067_ = lean_ctor_get(v___x_2055_, 0);
                    v_isSharedCheck_2074_ = (!lean_is_exclusive(v___x_2055_)) as u8;
                    if v_isSharedCheck_2074_ == 0 {
                        v___x_2069_ = v___x_2055_;
                        v_isShared_2070_ = v_isSharedCheck_2074_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2067_);
                        lean_dec(v___x_2055_);
                        v___x_2069_ = lean_box(0);
                        v_isShared_2070_ = v_isSharedCheck_2074_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2053_ == 0 {
                    lean_ctor_set(v___x_2052_, 1, v_a_2056_);
                    v___x_2061_ = v___x_2052_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_toSignature_2047_);
                    lean_ctor_set(v_reuseFailAlloc_2065_, 1, v_a_2056_);
                    lean_ctor_set(v_reuseFailAlloc_2065_, 2, v_inlineAttr_x3f_2050_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2065_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_recursive_2049_,
                    );
                    v___x_2061_ = v_reuseFailAlloc_2065_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2059_ == 0 {
                    lean_ctor_set(v___x_2058_, 0, v___x_2061_);
                    v___x_2063_ = v___x_2058_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2061_);
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
                    v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
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
    mut v_decl_2076_: *mut LeanObject,
    mut v_a_2077_: *mut LeanObject,
    mut v_a_2078_: *mut LeanObject,
    mut v_a_2079_: *mut LeanObject,
    mut v_a_2080_: *mut LeanObject,
    mut v_a_2081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2082_: *mut LeanObject = core::ptr::null_mut();
    v_res_2082_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase(
        v_decl_2076_,
        v_a_2077_,
        v_a_2078_,
        v_a_2079_,
        v_a_2080_,
    );
    lean_dec(v_a_2080_);
    lean_dec_ref(v_a_2079_);
    lean_dec(v_a_2078_);
    lean_dec_ref(v_a_2077_);
    return v_res_2082_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0(
    mut v_as_2083_: *mut LeanObject,
    mut v_i_2084_: usize,
    mut v_stop_2085_: usize,
) -> u8 {
    let mut v___x_2086_: u8 = 0;
    let mut v___x_2087_: u8 = 0;
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
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
                    if lean_obj_tag(v___x_2088_) == 2 {
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
    mut v_as_2093_: *mut LeanObject,
    mut v_i_2094_: *mut LeanObject,
    mut v_stop_2095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2096_: usize = 0;
    let mut v_stop_boxed_2097_: usize = 0;
    let mut v_res_2098_: u8 = 0;
    let mut v_r_2099_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2096_ = lean_unbox_usize(v_i_2094_);
    lean_dec(v_i_2094_);
    v_stop_boxed_2097_ = lean_unbox_usize(v_stop_2095_);
    lean_dec(v_stop_2095_);
    v_res_2098_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0(v_as_2093_, v_i_boxed_2096_, v_stop_boxed_2097_);
    lean_dec_ref(v_as_2093_);
    v_r_2099_ = lean_box((v_res_2098_) as usize);
    return v_r_2099_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ensureHasDefault(
    mut v_alts_2100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: u8 = 0;
    let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_last_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: u8 = 0;
    let mut v___x_2120_: usize = 0;
    let mut v___x_2121_: usize = 0;
    let mut v___x_2122_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2106_ = lean_unsigned_to_nat(0);
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
                v___x_2104_ = lean_alloc_ctor(2, 1, (0) as u32);
                lean_ctor_set(v___x_2104_, 0, v___y_2103_);
                v___x_2105_ = lean_array_push(v___y_2102_, v___x_2104_);
                return v___x_2105_;
            }
            2 => {
                v___x_2109_ = lean_unsigned_to_nat(2);
                v___x_2110_ = lean_nat_dec_lt(v___x_2107_, v___x_2109_);
                if v___x_2110_ == 0 {
                    v___x_2111_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0_once), _init_l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0);
                    v___x_2112_ = lean_unsigned_to_nat(1);
                    v___x_2113_ = lean_nat_sub(v___x_2107_, v___x_2112_);
                    v_last_2114_ = lean_array_get(v___x_2111_, v_alts_2100_, v___x_2113_);
                    lean_dec(v___x_2113_);
                    v_alts_2115_ = lean_array_pop(v_alts_2100_);
                    match lean_obj_tag(v_last_2114_) {
                        0 => {
                            v_code_2116_ = lean_ctor_get(v_last_2114_, 2);
                            lean_inc_ref(v_code_2116_);
                            lean_dec_ref_known(v_last_2114_, 3);
                            v___y_2102_ = v_alts_2115_;
                            v___y_2103_ = v_code_2116_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_2117_ = lean_ctor_get(v_last_2114_, 1);
                            lean_inc_ref(v_code_2117_);
                            lean_dec_ref_known(v_last_2114_, 2);
                            v___y_2102_ = v_alts_2115_;
                            v___y_2103_ = v_code_2117_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_2118_ = lean_ctor_get(v_last_2114_, 0);
                            lean_inc_ref(v_code_2118_);
                            lean_dec_ref_known(v_last_2114_, 1);
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
pub unsafe fn _init_l_Lean_Compiler_LCNF_simpCase___closed__3() -> *mut LeanObject {
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: u8 = 0;
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    v___x_2127_ = lean_unsigned_to_nat(0);
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
pub unsafe fn _init_l_Lean_Compiler_LCNF_simpCase() -> *mut LeanObject {
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    v___x_2132_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_simpCase___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_simpCase___closed__3_once),
        _init_l_Lean_Compiler_LCNF_simpCase___closed__3,
    );
    return v___x_2132_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: u8 = 0;
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    v___x_2203_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_;
    v___x_2204_ = 1;
    v___x_2205_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_;
    v___x_2206_ = l_Lean_registerTraceClass(v___x_2203_, v___x_2204_, v___x_2205_);
    return v___x_2206_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2____boxed(
    mut v_a_2207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2208_: *mut LeanObject = core::ptr::null_mut();
    v_res_2208_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_();
    return v_res_2208_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_SimpCase(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_AlphaEqv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Compiler_LCNF_simpCase = _init_l_Lean_Compiler_LCNF_simpCase();
    lean_mark_persistent(l_Lean_Compiler_LCNF_simpCase);
    res = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_SimpCase(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_SimpCase(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_AlphaEqv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_SimpCase(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_SimpCase(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_SimpCase(builtin);
}

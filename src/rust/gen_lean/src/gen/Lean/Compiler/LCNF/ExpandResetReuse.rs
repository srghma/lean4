// Lean compiler output
// Module: Lean.Compiler.LCNF.ExpandResetReuse
// Imports: Lean.Compiler.LCNF.PassManager Init.While
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_fset, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_pop, lean_array_push, lean_array_set, lean_array_size,
    lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_ptr_addr, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::{
    l_Array_append___redArg, l_Array_instInhabited, l_Array_reverse___redArg,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedForall___redArg___lam__0___boxed, l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Init::While::{initialize_Init_While, runtime_initialize_Init_While};
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg,
    l_Lean_Compiler_LCNF_Code_toCodeDecl_x21, l_Lean_Compiler_LCNF_attachCodeDecls,
    l_Lean_Compiler_LCNF_instInhabitedCode_default__1,
    l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg,
    l_Lean_Compiler_LCNF_eraseLetDecl___redArg, l_Lean_Compiler_LCNF_findLetValue_x3f___redArg,
    l_Lean_Compiler_LCNF_getConfig___redArg, l_Lean_Compiler_LCNF_mkFreshBinderName___redArg,
    l_Lean_Compiler_LCNF_mkFunDecl, l_Lean_Compiler_LCNF_mkLetDecl, l_Lean_Compiler_LCNF_mkParam,
};
use crate::r#gen::Lean::Compiler::LCNF::PassManager::{
    initialize_Lean_Compiler_LCNF_PassManager, l_Lean_Compiler_LCNF_Pass_mkPerDeclaration,
    runtime_initialize_Lean_Compiler_LCNF_PassManager,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_const___override, l_Lean_Expr_constName_x21, l_Lean_Expr_getAppFn,
    l_Lean_instBEqFVarId_beq,
};
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2_value) as *mut leanh::LeanObject;
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1_value: leanh::LeanStringObject<36> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 69, 120, 112, 97, 110, 100, 82, 101, 115, 101, 116, 82, 101, 117, 115, 101, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__2_value: leanh::LeanStringObject<82> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 82, m_capacity: 82, m_length: 81, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 69, 120, 112, 97, 110, 100, 82, 101, 115, 101, 116, 82, 101, 117, 115, 101, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 101, 114, 97, 115, 101, 80, 114, 111, 106, 73, 110, 99, 70, 111, 114, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__3_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 110, 32, 62, 32, 48, 32, 45, 45, 32, 48, 32, 105, 110, 99, 115, 32, 115, 104, 111, 117, 108, 100, 32, 110, 111, 116, 32, 98, 101, 32, 104, 97, 112, 112, 101, 110, 105, 110, 103, 10, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 111, 111, 108, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__1_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__0_value) as *mut leanh::LeanObject,12882480457794858234 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__1_value) as *mut leanh::LeanObject,15761733860085307253 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__3_value: leanh::LeanCtorObject<5> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__4_value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__0_value) as *mut leanh::LeanObject,12882480457794858234 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__4_value) as *mut leanh::LeanObject,9255189395584251158 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__6_value: leanh::LeanCtorObject<5> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__0_value: leanh::LeanStringObject<76> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 76, m_capacity: 76, m_length: 75, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 69, 120, 112, 97, 110, 100, 82, 101, 115, 101, 116, 82, 101, 117, 115, 101, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 114, 101, 109, 97, 112, 83, 101, 116, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1_value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__0_value: leanh::LeanStringObject<84> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 84, m_capacity: 84, m_length: 83, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 69, 120, 112, 97, 110, 100, 82, 101, 115, 101, 116, 82, 101, 117, 115, 101, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 112, 97, 114, 116, 105, 116, 105, 111, 110, 83, 101, 108, 102, 83, 101, 116, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___closed__0_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [117, 110, 117, 115, 101, 100, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject,8495011437180164029 as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 111, 98, 106, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject,930430701391226905 as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__3_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__0_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [114, 101, 117, 115, 101, 70, 97, 105, 108, 65, 108, 108, 111, 99, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__0_value) as *mut leanh::LeanObject,1965393245545708194 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__1_value) as *mut leanh::LeanObject;
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 117, 115, 101, 106, 112, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__0_value) as *mut leanh::LeanObject,16585790626105456024 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__2_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [85, 73, 110, 116, 56, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__2_value) as *mut leanh::LeanObject,15764114953608429200 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__6_value: leanh::LeanStringObject<84> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 84, m_capacity: 84, m_length: 83, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 110, 32, 61, 61, 32, 49, 32, 45, 45, 32, 110, 32, 109, 117, 115, 116, 32, 98, 101, 32, 111, 110, 101, 32, 115, 105, 110, 99, 101, 32, 96, 114, 101, 115, 101, 116, 84, 111, 107, 101, 110, 32, 58, 61, 32, 114, 101, 115, 101, 116, 32, 46, 46, 46, 96, 10, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5_value: leanh::LeanStringObject<83> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 83, m_capacity: 83, m_length: 82, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 69, 120, 112, 97, 110, 100, 82, 101, 115, 101, 116, 82, 101, 117, 115, 101, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 112, 114, 111, 99, 101, 115, 115, 82, 101, 115, 101, 116, 67, 111, 110, 116, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__0_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 115, 83, 104, 97, 114, 101, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__0_value) as *mut leanh::LeanObject,16304350630193599974 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__2_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 115, 101, 116, 106, 112, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__2_value) as *mut leanh::LeanObject,7530470289044155581 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__4_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [105, 115, 83, 104, 97, 114, 101, 100, 67, 104, 101, 99, 107, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__4_value) as *mut leanh::LeanObject,8080113652283748063 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_expandResetReuse___closed__0_value: leanh::LeanStringObject<
    17,
> = leanh::LeanStringObject {
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
        101, 120, 112, 97, 110, 100, 82, 101, 115, 101, 116, 82, 101, 117, 115, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_expandResetReuse___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_expandResetReuse___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_expandResetReuse___closed__1_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_expandResetReuse___closed__0_value)
            as *mut leanh::LeanObject,
        14075296980557281220 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_expandResetReuse___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_expandResetReuse___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_expandResetReuse___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Compiler_LCNF_expandResetReuse___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_expandResetReuse___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_expandResetReuse___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_expandResetReuse___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_expandResetReuse: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2042452093243897853 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_expandResetReuse___closed__0_value) as *mut leanh::LeanObject,4700002501560739034 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1501781890156459336 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4203849195465939425 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [69, 120, 112, 97, 110, 100, 82, 101, 115, 101, 116, 82, 101, 117, 115, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4716892160583994151 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,5381860422951367578 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6136025083668818235 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,131487144209835133 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15922225652527654984 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10324035721225016549 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14500088037220215128 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6052734082724814545 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7077821464577668063 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16536633794523358290 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16492176252976513240 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2642_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_2642_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2645_ = l_Array_instInhabited(leanh::lean_box(0));
    return v___x_2645_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0(
    mut v_msg_2646_: *mut leanh::LeanObject,
    mut v___y_2647_: *mut leanh::LeanObject,
    mut v___y_2648_: *mut leanh::LeanObject,
    mut v___y_2649_: *mut leanh::LeanObject,
    mut v___y_2650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2657_: u8 = 0;
    let mut v_toFunctor_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2664_: u8 = 0;
    let mut v___f_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915__overap_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2688_: u8 = 0;
    let mut v_unused_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2690_: u8 = 0;
    let mut v_unused_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2652_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0);
                v___x_2653_ = l_StateRefT_x27_instMonad___redArg(v___x_2652_);
                v_toApplicative_2654_ = leanh::lean_ctor_get(v___x_2653_, 0);
                v_isSharedCheck_2690_ = (!leanh::lean_is_exclusive(v___x_2653_)) as u8;
                if v_isSharedCheck_2690_ == 0 {
                    v_unused_2691_ = leanh::lean_ctor_get(v___x_2653_, 1);
                    leanh::lean_dec(v_unused_2691_);
                    v___x_2656_ = v___x_2653_;
                    v_isShared_2657_ = v_isSharedCheck_2690_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_2654_);
                    leanh::lean_dec(v___x_2653_);
                    v___x_2656_ = leanh::lean_box(0);
                    v_isShared_2657_ = v_isSharedCheck_2690_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2658_ = leanh::lean_ctor_get(v_toApplicative_2654_, 0);
                v_toSeq_2659_ = leanh::lean_ctor_get(v_toApplicative_2654_, 2);
                v_toSeqLeft_2660_ = leanh::lean_ctor_get(v_toApplicative_2654_, 3);
                v_toSeqRight_2661_ = leanh::lean_ctor_get(v_toApplicative_2654_, 4);
                v_isSharedCheck_2688_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_2654_)) as u8;
                if v_isSharedCheck_2688_ == 0 {
                    v_unused_2689_ = leanh::lean_ctor_get(v_toApplicative_2654_, 1);
                    leanh::lean_dec(v_unused_2689_);
                    v___x_2663_ = v_toApplicative_2654_;
                    v_isShared_2664_ = v_isSharedCheck_2688_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_2661_);
                    leanh::lean_inc(v_toSeqLeft_2660_);
                    leanh::lean_inc(v_toSeq_2659_);
                    leanh::lean_inc(v_toFunctor_2658_);
                    leanh::lean_dec(v_toApplicative_2654_);
                    v___x_2663_ = leanh::lean_box(0);
                    v_isShared_2664_ = v_isSharedCheck_2688_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2665_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1;
                v___f_2666_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2;
                leanh::lean_inc_ref(v_toFunctor_2658_);
                v___f_2667_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2667_, 0, v_toFunctor_2658_);
                v___f_2668_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2668_, 0, v_toFunctor_2658_);
                v___x_2669_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2669_, 0, v___f_2667_);
                leanh::lean_ctor_set(v___x_2669_, 1, v___f_2668_);
                v___f_2670_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2670_, 0, v_toSeqRight_2661_);
                v___f_2671_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2671_, 0, v_toSeqLeft_2660_);
                v___f_2672_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2672_, 0, v_toSeq_2659_);
                if v_isShared_2664_ == 0 {
                    leanh::lean_ctor_set(v___x_2663_, 4, v___f_2670_);
                    leanh::lean_ctor_set(v___x_2663_, 3, v___f_2671_);
                    leanh::lean_ctor_set(v___x_2663_, 2, v___f_2672_);
                    leanh::lean_ctor_set(v___x_2663_, 1, v___f_2665_);
                    leanh::lean_ctor_set(v___x_2663_, 0, v___x_2669_);
                    v___x_2674_ = v___x_2663_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2687_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2669_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2687_, 1, v___f_2665_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2687_, 2, v___f_2672_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2687_, 3, v___f_2671_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2687_, 4, v___f_2670_);
                    v___x_2674_ = v_reuseFailAlloc_2687_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2657_ == 0 {
                    leanh::lean_ctor_set(v___x_2656_, 1, v___f_2666_);
                    leanh::lean_ctor_set(v___x_2656_, 0, v___x_2674_);
                    v___x_2676_ = v___x_2656_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2686_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2674_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2686_, 1, v___f_2666_);
                    v___x_2676_ = v_reuseFailAlloc_2686_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2677_ = l_StateRefT_x27_instMonad___redArg(v___x_2676_);
                v___x_2678_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3);
                v___x_2679_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2679_, 0, v___x_2678_);
                leanh::lean_ctor_set(v___x_2679_, 1, v___x_2678_);
                v___x_2680_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2680_, 0, v___x_2678_);
                leanh::lean_ctor_set(v___x_2680_, 1, v___x_2679_);
                v___x_2681_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2681_, 0, v___x_2680_);
                v___x_2682_ = l_instInhabitedOfMonad___redArg(v___x_2677_, v___x_2681_);
                v___f_2683_ = leanh::lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_2683_, 0, v___x_2682_);
                v___x_2915__overap_2684_ = lean_panic_fn_borrowed(v___f_2683_, v_msg_2646_);
                leanh::lean_dec_ref(v___f_2683_);
                leanh::lean_inc(v___y_2650_);
                leanh::lean_inc_ref(v___y_2649_);
                leanh::lean_inc(v___y_2648_);
                leanh::lean_inc_ref(v___y_2647_);
                v___x_2685_ = leanh::lean_apply_5(
                    v___x_2915__overap_2684_,
                    v___y_2647_,
                    v___y_2648_,
                    v___y_2649_,
                    v___y_2650_,
                    leanh::lean_box(0),
                );
                return v___x_2685_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___boxed(
    mut v_msg_2692_: *mut leanh::LeanObject,
    mut v___y_2693_: *mut leanh::LeanObject,
    mut v___y_2694_: *mut leanh::LeanObject,
    mut v___y_2695_: *mut leanh::LeanObject,
    mut v___y_2696_: *mut leanh::LeanObject,
    mut v___y_2697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2698_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0(v_msg_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
    leanh::lean_dec(v___y_2696_);
    leanh::lean_dec_ref(v___y_2695_);
    leanh::lean_dec(v___y_2694_);
    leanh::lean_dec_ref(v___y_2693_);
    return v_res_2698_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(
    mut v_fst_2699_: *mut leanh::LeanObject,
    mut v_snd_2700_: *mut leanh::LeanObject,
    mut v_fst_2701_: *mut leanh::LeanObject,
    mut v_x_2702_: *mut leanh::LeanObject,
    mut v___y_2703_: *mut leanh::LeanObject,
    mut v___y_2704_: *mut leanh::LeanObject,
    mut v___y_2705_: *mut leanh::LeanObject,
    mut v___y_2706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2708_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2708_, 0, v_fst_2699_);
    leanh::lean_ctor_set(v___x_2708_, 1, v_snd_2700_);
    v___x_2709_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2709_, 0, v_fst_2701_);
    leanh::lean_ctor_set(v___x_2709_, 1, v___x_2708_);
    v___x_2710_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2710_, 0, v___x_2709_);
    v___x_2711_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2711_, 0, v___x_2710_);
    return v___x_2711_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0___boxed(
    mut v_fst_2712_: *mut leanh::LeanObject,
    mut v_snd_2713_: *mut leanh::LeanObject,
    mut v_fst_2714_: *mut leanh::LeanObject,
    mut v_x_2715_: *mut leanh::LeanObject,
    mut v___y_2716_: *mut leanh::LeanObject,
    mut v___y_2717_: *mut leanh::LeanObject,
    mut v___y_2718_: *mut leanh::LeanObject,
    mut v___y_2719_: *mut leanh::LeanObject,
    mut v___y_2720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2721_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_2712_, v_snd_2713_, v_fst_2714_, v_x_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
    leanh::lean_dec(v___y_2719_);
    leanh::lean_dec_ref(v___y_2718_);
    leanh::lean_dec(v___y_2717_);
    leanh::lean_dec_ref(v___y_2716_);
    leanh::lean_dec_ref(v_x_2715_);
    return v_res_2721_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2722_: u8 = 0;
    let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2722_ = 1;
    v___x_2723_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(v___x_2722_);
    return v___x_2723_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2727_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__3;
    v___x_2728_ = leanh::lean_unsigned_to_nat(6);
    v___x_2729_ = leanh::lean_unsigned_to_nat(87);
    v___x_2730_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__2;
    v___x_2731_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1;
    v___x_2732_ = l_mkPanicMessageWithDecl(
        v___x_2731_,
        v___x_2730_,
        v___x_2729_,
        v___x_2728_,
        v___x_2727_,
    );
    return v___x_2732_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(
    mut v_targetId_2733_: *mut leanh::LeanObject,
    mut v_a_2734_: *mut leanh::LeanObject,
    mut v___y_2735_: *mut leanh::LeanObject,
    mut v___y_2736_: *mut leanh::LeanObject,
    mut v___y_2737_: *mut leanh::LeanObject,
    mut v___y_2738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2752_: u8 = 0;
    let mut v_a_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2759_: u8 = 0;
    let mut v_a_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2763_: u8 = 0;
    let mut v___x_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2767_: u8 = 0;
    let mut v_snd_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2772_: u8 = 0;
    let mut v_fst_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2777_: u8 = 0;
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: u8 = 0;
    let mut v___x_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2814_: u8 = 0;
    let mut v_fvarId_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2820_: u8 = 0;
    let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2828_: u8 = 0;
    let mut v_unused_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2830_: u8 = 0;
    let mut v_unused_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_2834_: u8 = 0;
    let mut v_persistent_2835_: u8 = 0;
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: u8 = 0;
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2848_: u8 = 0;
    let mut v___x_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2860_: u8 = 0;
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: u8 = 0;
    let mut v___x_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2872_: u8 = 0;
    let mut v_unused_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: u8 = 0;
    let mut v___x_2887_: u8 = 0;
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2890_: u8 = 0;
    let mut v_fvarId_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2896_: u8 = 0;
    let mut v___x_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2904_: u8 = 0;
    let mut v_unused_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2906_: u8 = 0;
    let mut v_unused_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2910_: u8 = 0;
    let mut v_isSharedCheck_2911_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_2768_ = leanh::lean_ctor_get(v_a_2734_, 1);
                v_fst_2769_ = leanh::lean_ctor_get(v_a_2734_, 0);
                v_isSharedCheck_2911_ = (!leanh::lean_is_exclusive(v_a_2734_)) as u8;
                if v_isSharedCheck_2911_ == 0 {
                    v___x_2771_ = v_a_2734_;
                    v_isShared_2772_ = v_isSharedCheck_2911_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2768_);
                    leanh::lean_inc(v_fst_2769_);
                    leanh::lean_dec(v_a_2734_);
                    v___x_2771_ = leanh::lean_box(0);
                    v_isShared_2772_ = v_isSharedCheck_2911_;
                    state = 7;
                    continue;
                }
            }
            1 => {
                v___x_2744_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2744_, 0, v___y_2743_);
                leanh::lean_ctor_set(v___x_2744_, 1, v___y_2741_);
                v___x_2745_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2745_, 0, v___y_2742_);
                leanh::lean_ctor_set(v___x_2745_, 1, v___x_2744_);
                v_a_2734_ = v___x_2745_;
                state = 0;
                continue;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_2748_) == 0 {
                    v_a_2749_ = leanh::lean_ctor_get(v___y_2748_, 0);
                    v_isSharedCheck_2759_ = (!leanh::lean_is_exclusive(v___y_2748_)) as u8;
                    if v_isSharedCheck_2759_ == 0 {
                        v___x_2751_ = v___y_2748_;
                        v_isShared_2752_ = v_isSharedCheck_2759_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2749_);
                        leanh::lean_dec(v___y_2748_);
                        v___x_2751_ = leanh::lean_box(0);
                        v_isShared_2752_ = v_isSharedCheck_2759_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_2760_ = leanh::lean_ctor_get(v___y_2748_, 0);
                    v_isSharedCheck_2767_ = (!leanh::lean_is_exclusive(v___y_2748_)) as u8;
                    if v_isSharedCheck_2767_ == 0 {
                        v___x_2762_ = v___y_2748_;
                        v_isShared_2763_ = v_isSharedCheck_2767_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2760_);
                        leanh::lean_dec(v___y_2748_);
                        v___x_2762_ = leanh::lean_box(0);
                        v_isShared_2763_ = v_isSharedCheck_2767_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_a_2749_) == 0 {
                    v_a_2753_ = leanh::lean_ctor_get(v_a_2749_, 0);
                    leanh::lean_inc(v_a_2753_);
                    leanh::lean_dec_ref_known(v_a_2749_, 1);
                    if v_isShared_2752_ == 0 {
                        leanh::lean_ctor_set(v___x_2751_, 0, v_a_2753_);
                        v___x_2755_ = v___x_2751_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2756_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_a_2753_);
                        v___x_2755_ = v_reuseFailAlloc_2756_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2751_);
                    v_a_2757_ = leanh::lean_ctor_get(v_a_2749_, 0);
                    leanh::lean_inc(v_a_2757_);
                    leanh::lean_dec_ref_known(v_a_2749_, 1);
                    v_a_2734_ = v_a_2757_;
                    state = 0;
                    continue;
                }
            }
            4 => {
                return v___x_2755_;
            }
            5 => {
                if v_isShared_2763_ == 0 {
                    v___x_2765_ = v___x_2762_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2766_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
                    v___x_2765_ = v_reuseFailAlloc_2766_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2765_;
            }
            7 => {
                v_fst_2773_ = leanh::lean_ctor_get(v_snd_2768_, 0);
                v_snd_2774_ = leanh::lean_ctor_get(v_snd_2768_, 1);
                v_isSharedCheck_2910_ = (!leanh::lean_is_exclusive(v_snd_2768_)) as u8;
                if v_isSharedCheck_2910_ == 0 {
                    v___x_2776_ = v_snd_2768_;
                    v_isShared_2777_ = v_isSharedCheck_2910_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2774_);
                    leanh::lean_inc(v_fst_2773_);
                    leanh::lean_dec(v_snd_2768_);
                    v___x_2776_ = leanh::lean_box(0);
                    v_isShared_2777_ = v_isSharedCheck_2910_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2778_ = leanh::lean_unsigned_to_nat(2);
                v___x_2779_ = lean_array_get_size(v_fst_2769_);
                v___x_2780_ = lean_nat_dec_le(v___x_2778_, v___x_2779_);
                if v___x_2780_ == 0 {
                    if v_isShared_2777_ == 0 {
                        v___x_2782_ = v___x_2776_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2787_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_fst_2773_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2787_, 1, v_snd_2774_);
                        v___x_2782_ = v_reuseFailAlloc_2787_;
                        state = 9;
                        continue;
                    }
                } else {
                    v___x_2788_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0);
                    v___x_2789_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2790_ = lean_nat_sub(v___x_2779_, v___x_2789_);
                    v___x_2791_ = lean_array_get(v___x_2788_, v_fst_2769_, v___x_2790_);
                    leanh::lean_dec(v___x_2790_);
                    match leanh::lean_obj_tag(v___x_2791_) {
                        0 => {
                            v_decl_2792_ = leanh::lean_ctor_get(v___x_2791_, 0);
                            leanh::lean_inc_ref(v_decl_2792_);
                            v_value_2793_ = leanh::lean_ctor_get(v_decl_2792_, 3);
                            leanh::lean_inc(v_value_2793_);
                            match leanh::lean_obj_tag(v_value_2793_) {
                                8 => {
                                    leanh::lean_dec_ref_known(v_value_2793_, 3);
                                    leanh::lean_dec_ref(v_decl_2792_);
                                    v___x_2794_ = lean_array_pop(v_fst_2769_);
                                    v___x_2795_ = lean_array_push(v_fst_2773_, v___x_2791_);
                                    if v_isShared_2777_ == 0 {
                                        leanh::lean_ctor_set(v___x_2776_, 0, v___x_2795_);
                                        v___x_2797_ = v___x_2776_;
                                        state = 11;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2802_ =
                                            leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2802_,
                                            0,
                                            v___x_2795_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2802_,
                                            1,
                                            v_snd_2774_,
                                        );
                                        v___x_2797_ = v_reuseFailAlloc_2802_;
                                        state = 11;
                                        continue;
                                    }
                                }
                                7 => {
                                    leanh::lean_dec_ref_known(v_value_2793_, 2);
                                    leanh::lean_dec_ref(v_decl_2792_);
                                    v___x_2803_ = lean_array_pop(v_fst_2769_);
                                    v___x_2804_ = lean_array_push(v_fst_2773_, v___x_2791_);
                                    if v_isShared_2777_ == 0 {
                                        leanh::lean_ctor_set(v___x_2776_, 0, v___x_2804_);
                                        v___x_2806_ = v___x_2776_;
                                        state = 13;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2811_ =
                                            leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2811_,
                                            0,
                                            v___x_2804_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2811_,
                                            1,
                                            v_snd_2774_,
                                        );
                                        v___x_2806_ = v_reuseFailAlloc_2811_;
                                        state = 13;
                                        continue;
                                    }
                                }
                                _ => {
                                    leanh::lean_del_object(v___x_2776_);
                                    leanh::lean_del_object(v___x_2771_);
                                    v_isSharedCheck_2830_ =
                                        (!leanh::lean_is_exclusive(v___x_2791_)) as u8;
                                    if v_isSharedCheck_2830_ == 0 {
                                        v_unused_2831_ =
                                            leanh::lean_ctor_get(v___x_2791_, 0);
                                        leanh::lean_dec(v_unused_2831_);
                                        v___x_2813_ = v___x_2791_;
                                        v_isShared_2814_ = v_isSharedCheck_2830_;
                                        state = 15;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_2791_);
                                        v___x_2813_ = leanh::lean_box(0);
                                        v_isShared_2814_ = v_isSharedCheck_2830_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            }
                        }
                        7 => {
                            v_fvarId_2832_ = leanh::lean_ctor_get(v___x_2791_, 0);
                            v_n_2833_ = leanh::lean_ctor_get(v___x_2791_, 1);
                            v_check_2834_ = leanh::lean_ctor_get_uint8(
                                v___x_2791_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                            );
                            v_persistent_2835_ = leanh::lean_ctor_get_uint8(
                                v___x_2791_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1)
                                    as u32,
                            );
                            v___x_2836_ = leanh::lean_unsigned_to_nat(0);
                            v___x_2837_ = lean_nat_dec_lt(v___x_2836_, v_n_2833_);
                            if v___x_2837_ == 0 {
                                leanh::lean_dec_ref_known(v___x_2791_, 2);
                                leanh::lean_del_object(v___x_2776_);
                                leanh::lean_dec(v_snd_2774_);
                                leanh::lean_dec(v_fst_2773_);
                                leanh::lean_del_object(v___x_2771_);
                                leanh::lean_dec(v_fst_2769_);
                                v___x_2838_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4);
                                v___x_2839_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0(v___x_2838_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
                                v___y_2748_ = v___x_2839_;
                                state = 2;
                                continue;
                            } else {
                                v___x_2840_ = lean_nat_sub(v___x_2779_, v___x_2778_);
                                v___x_2841_ = lean_array_get(v___x_2788_, v_fst_2769_, v___x_2840_);
                                leanh::lean_dec(v___x_2840_);
                                if leanh::lean_obj_tag(v___x_2841_) == 0 {
                                    v_decl_2842_ = leanh::lean_ctor_get(v___x_2841_, 0);
                                    leanh::lean_inc_ref(v_decl_2842_);
                                    v_value_2843_ = leanh::lean_ctor_get(v_decl_2842_, 3);
                                    leanh::lean_inc(v_value_2843_);
                                    if leanh::lean_obj_tag(v_value_2843_) == 6 {
                                        v_fvarId_2844_ =
                                            leanh::lean_ctor_get(v_decl_2842_, 0);
                                        leanh::lean_inc(v_fvarId_2844_);
                                        leanh::lean_dec_ref(v_decl_2842_);
                                        v_i_2845_ = leanh::lean_ctor_get(v_value_2843_, 0);
                                        leanh::lean_inc(v_i_2845_);
                                        v_var_2846_ = leanh::lean_ctor_get(v_value_2843_, 1);
                                        leanh::lean_inc(v_var_2846_);
                                        leanh::lean_dec_ref_known(v_value_2843_, 2);
                                        v___x_2886_ = l_Lean_instBEqFVarId_beq(
                                            v_fvarId_2844_,
                                            v_fvarId_2832_,
                                        );
                                        leanh::lean_dec(v_fvarId_2844_);
                                        if v___x_2886_ == 0 {
                                            leanh::lean_dec(v_var_2846_);
                                            v___y_2848_ = v___x_2886_;
                                            state = 19;
                                            continue;
                                        } else {
                                            v___x_2887_ = l_Lean_instBEqFVarId_beq(
                                                v_targetId_2733_,
                                                v_var_2846_,
                                            );
                                            leanh::lean_dec(v_var_2846_);
                                            v___y_2848_ = v___x_2887_;
                                            state = 19;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec_ref_known(v___x_2791_, 2);
                                        leanh::lean_del_object(v___x_2776_);
                                        leanh::lean_del_object(v___x_2771_);
                                        v_isSharedCheck_2906_ =
                                            (!leanh::lean_is_exclusive(v___x_2841_)) as u8;
                                        if v_isSharedCheck_2906_ == 0 {
                                            v_unused_2907_ =
                                                leanh::lean_ctor_get(v___x_2841_, 0);
                                            leanh::lean_dec(v_unused_2907_);
                                            v___x_2889_ = v___x_2841_;
                                            v_isShared_2890_ = v_isSharedCheck_2906_;
                                            state = 26;
                                            continue;
                                        } else {
                                            leanh::lean_dec(v___x_2841_);
                                            v___x_2889_ = leanh::lean_box(0);
                                            v_isShared_2890_ = v_isSharedCheck_2906_;
                                            state = 26;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref_known(v___x_2791_, 2);
                                    leanh::lean_del_object(v___x_2776_);
                                    leanh::lean_del_object(v___x_2771_);
                                    v___x_2908_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_2773_, v_snd_2774_, v_fst_2769_, v___x_2841_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
                                    leanh::lean_dec(v___x_2841_);
                                    v___y_2748_ = v___x_2908_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                        _ => {
                            leanh::lean_del_object(v___x_2776_);
                            leanh::lean_del_object(v___x_2771_);
                            v___x_2909_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_2773_, v_snd_2774_, v_fst_2769_, v___x_2791_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
                            leanh::lean_dec(v___x_2791_);
                            v___y_2748_ = v___x_2909_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            9 => {
                if v_isShared_2772_ == 0 {
                    leanh::lean_ctor_set(v___x_2771_, 1, v___x_2782_);
                    v___x_2784_ = v___x_2771_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2786_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_fst_2769_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2786_, 1, v___x_2782_);
                    v___x_2784_ = v_reuseFailAlloc_2786_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_2785_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2785_, 0, v___x_2784_);
                return v___x_2785_;
            }
            11 => {
                if v_isShared_2772_ == 0 {
                    leanh::lean_ctor_set(v___x_2771_, 1, v___x_2797_);
                    leanh::lean_ctor_set(v___x_2771_, 0, v___x_2794_);
                    v___x_2799_ = v___x_2771_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2801_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2794_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2801_, 1, v___x_2797_);
                    v___x_2799_ = v_reuseFailAlloc_2801_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v_a_2734_ = v___x_2799_;
                state = 0;
                continue;
            }
            13 => {
                if v_isShared_2772_ == 0 {
                    leanh::lean_ctor_set(v___x_2771_, 1, v___x_2806_);
                    leanh::lean_ctor_set(v___x_2771_, 0, v___x_2803_);
                    v___x_2808_ = v___x_2771_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2810_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2810_, 0, v___x_2803_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2810_, 1, v___x_2806_);
                    v___x_2808_ = v_reuseFailAlloc_2810_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v_a_2734_ = v___x_2808_;
                state = 0;
                continue;
            }
            15 => {
                v_fvarId_2815_ = leanh::lean_ctor_get(v_decl_2792_, 0);
                v_binderName_2816_ = leanh::lean_ctor_get(v_decl_2792_, 1);
                v_type_2817_ = leanh::lean_ctor_get(v_decl_2792_, 2);
                v_isSharedCheck_2828_ = (!leanh::lean_is_exclusive(v_decl_2792_)) as u8;
                if v_isSharedCheck_2828_ == 0 {
                    v_unused_2829_ = leanh::lean_ctor_get(v_decl_2792_, 3);
                    leanh::lean_dec(v_unused_2829_);
                    v___x_2819_ = v_decl_2792_;
                    v_isShared_2820_ = v_isSharedCheck_2828_;
                    state = 16;
                    continue;
                } else {
                    leanh::lean_inc(v_type_2817_);
                    leanh::lean_inc(v_binderName_2816_);
                    leanh::lean_inc(v_fvarId_2815_);
                    leanh::lean_dec(v_decl_2792_);
                    v___x_2819_ = leanh::lean_box(0);
                    v_isShared_2820_ = v_isSharedCheck_2828_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_2820_ == 0 {
                    v___x_2822_ = v___x_2819_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2827_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_fvarId_2815_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2827_, 1, v_binderName_2816_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2827_, 2, v_type_2817_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2827_, 3, v_value_2793_);
                    v___x_2822_ = v_reuseFailAlloc_2827_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_2814_ == 0 {
                    leanh::lean_ctor_set(v___x_2813_, 0, v___x_2822_);
                    v___x_2824_ = v___x_2813_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2826_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2822_);
                    v___x_2824_ = v_reuseFailAlloc_2826_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_2825_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_2773_, v_snd_2774_, v_fst_2769_, v___x_2824_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
                leanh::lean_dec_ref(v___x_2824_);
                v___y_2748_ = v___x_2825_;
                state = 2;
                continue;
            }
            19 => {
                if v___y_2848_ == 0 {
                    leanh::lean_dec(v_i_2845_);
                    leanh::lean_dec_ref_known(v___x_2841_, 1);
                    leanh::lean_dec_ref_known(v___x_2791_, 2);
                    if v_isShared_2777_ == 0 {
                        v___x_2850_ = v___x_2776_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_2855_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_fst_2773_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2855_, 1, v_snd_2774_);
                        v___x_2850_ = v_reuseFailAlloc_2855_;
                        state = 20;
                        continue;
                    }
                } else {
                    v___x_2856_ = leanh::lean_box(0);
                    v___x_2857_ = lean_array_get_borrowed(v___x_2856_, v_snd_2774_, v_i_2845_);
                    if leanh::lean_obj_tag(v___x_2857_) == 0 {
                        leanh::lean_inc(v_n_2833_);
                        leanh::lean_inc(v_fvarId_2832_);
                        leanh::lean_del_object(v___x_2776_);
                        leanh::lean_del_object(v___x_2771_);
                        v_isSharedCheck_2872_ =
                            (!leanh::lean_is_exclusive(v___x_2791_)) as u8;
                        if v_isSharedCheck_2872_ == 0 {
                            v_unused_2873_ = leanh::lean_ctor_get(v___x_2791_, 1);
                            leanh::lean_dec(v_unused_2873_);
                            v_unused_2874_ = leanh::lean_ctor_get(v___x_2791_, 0);
                            leanh::lean_dec(v_unused_2874_);
                            v___x_2859_ = v___x_2791_;
                            v_isShared_2860_ = v_isSharedCheck_2872_;
                            state = 22;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_2791_);
                            v___x_2859_ = leanh::lean_box(0);
                            v_isShared_2860_ = v_isSharedCheck_2872_;
                            state = 22;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_i_2845_);
                        v___x_2875_ = lean_array_push(v_fst_2773_, v___x_2791_);
                        v___x_2876_ = lean_array_push(v___x_2875_, v___x_2841_);
                        v___x_2877_ = lean_array_pop(v_fst_2769_);
                        v___x_2878_ = lean_array_pop(v___x_2877_);
                        if v_isShared_2777_ == 0 {
                            leanh::lean_ctor_set(v___x_2776_, 0, v___x_2876_);
                            v___x_2880_ = v___x_2776_;
                            state = 24;
                            continue;
                        } else {
                            v_reuseFailAlloc_2885_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2885_, 0, v___x_2876_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2885_, 1, v_snd_2774_);
                            v___x_2880_ = v_reuseFailAlloc_2885_;
                            state = 24;
                            continue;
                        }
                    }
                }
            }
            20 => {
                if v_isShared_2772_ == 0 {
                    leanh::lean_ctor_set(v___x_2771_, 1, v___x_2850_);
                    v___x_2852_ = v___x_2771_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2854_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_fst_2769_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2854_, 1, v___x_2850_);
                    v___x_2852_ = v_reuseFailAlloc_2854_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_2853_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2853_, 0, v___x_2852_);
                return v___x_2853_;
            }
            22 => {
                v___x_2861_ = lean_array_pop(v_fst_2769_);
                v___x_2862_ = lean_array_pop(v___x_2861_);
                leanh::lean_inc(v_fvarId_2832_);
                v___x_2863_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2863_, 0, v_fvarId_2832_);
                v___x_2864_ = lean_array_set(v_snd_2774_, v_i_2845_, v___x_2863_);
                leanh::lean_dec(v_i_2845_);
                v___x_2865_ = lean_array_push(v_fst_2773_, v___x_2841_);
                v___x_2866_ = lean_nat_dec_eq(v_n_2833_, v___x_2789_);
                if v___x_2866_ == 0 {
                    v___x_2867_ = lean_nat_sub(v_n_2833_, v___x_2789_);
                    leanh::lean_dec(v_n_2833_);
                    if v_isShared_2860_ == 0 {
                        leanh::lean_ctor_set(v___x_2859_, 1, v___x_2867_);
                        v___x_2869_ = v___x_2859_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_2871_ = leanh::lean_alloc_ctor(7, 2, (2) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_fvarId_2832_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2871_, 1, v___x_2867_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2871_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                            v_check_2834_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2871_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                            v_persistent_2835_,
                        );
                        v___x_2869_ = v_reuseFailAlloc_2871_;
                        state = 23;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2859_);
                    leanh::lean_dec(v_n_2833_);
                    leanh::lean_dec(v_fvarId_2832_);
                    v___y_2741_ = v___x_2864_;
                    v___y_2742_ = v___x_2862_;
                    v___y_2743_ = v___x_2865_;
                    state = 1;
                    continue;
                }
            }
            23 => {
                v___x_2870_ = lean_array_push(v___x_2865_, v___x_2869_);
                v___y_2741_ = v___x_2864_;
                v___y_2742_ = v___x_2862_;
                v___y_2743_ = v___x_2870_;
                state = 1;
                continue;
            }
            24 => {
                if v_isShared_2772_ == 0 {
                    leanh::lean_ctor_set(v___x_2771_, 1, v___x_2880_);
                    leanh::lean_ctor_set(v___x_2771_, 0, v___x_2878_);
                    v___x_2882_ = v___x_2771_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_2884_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2878_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2884_, 1, v___x_2880_);
                    v___x_2882_ = v_reuseFailAlloc_2884_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                v_a_2734_ = v___x_2882_;
                state = 0;
                continue;
            }
            26 => {
                v_fvarId_2891_ = leanh::lean_ctor_get(v_decl_2842_, 0);
                v_binderName_2892_ = leanh::lean_ctor_get(v_decl_2842_, 1);
                v_type_2893_ = leanh::lean_ctor_get(v_decl_2842_, 2);
                v_isSharedCheck_2904_ = (!leanh::lean_is_exclusive(v_decl_2842_)) as u8;
                if v_isSharedCheck_2904_ == 0 {
                    v_unused_2905_ = leanh::lean_ctor_get(v_decl_2842_, 3);
                    leanh::lean_dec(v_unused_2905_);
                    v___x_2895_ = v_decl_2842_;
                    v_isShared_2896_ = v_isSharedCheck_2904_;
                    state = 27;
                    continue;
                } else {
                    leanh::lean_inc(v_type_2893_);
                    leanh::lean_inc(v_binderName_2892_);
                    leanh::lean_inc(v_fvarId_2891_);
                    leanh::lean_dec(v_decl_2842_);
                    v___x_2895_ = leanh::lean_box(0);
                    v_isShared_2896_ = v_isSharedCheck_2904_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_2896_ == 0 {
                    v___x_2898_ = v___x_2895_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2903_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_fvarId_2891_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_binderName_2892_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2903_, 2, v_type_2893_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2903_, 3, v_value_2843_);
                    v___x_2898_ = v_reuseFailAlloc_2903_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_2890_ == 0 {
                    leanh::lean_ctor_set(v___x_2889_, 0, v___x_2898_);
                    v___x_2900_ = v___x_2889_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_2902_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2898_);
                    v___x_2900_ = v_reuseFailAlloc_2902_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                v___x_2901_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_2773_, v_snd_2774_, v_fst_2769_, v___x_2900_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
                leanh::lean_dec_ref(v___x_2900_);
                v___y_2748_ = v___x_2901_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___boxed(
    mut v_targetId_2912_: *mut leanh::LeanObject,
    mut v_a_2913_: *mut leanh::LeanObject,
    mut v___y_2914_: *mut leanh::LeanObject,
    mut v___y_2915_: *mut leanh::LeanObject,
    mut v___y_2916_: *mut leanh::LeanObject,
    mut v___y_2917_: *mut leanh::LeanObject,
    mut v___y_2918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2919_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(v_targetId_2912_, v_a_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
    leanh::lean_dec(v___y_2917_);
    leanh::lean_dec_ref(v___y_2916_);
    leanh::lean_dec(v___y_2915_);
    leanh::lean_dec_ref(v___y_2914_);
    leanh::lean_dec(v_targetId_2912_);
    return v_res_2919_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(
    mut v_nFields_2922_: *mut leanh::LeanObject,
    mut v_targetId_2923_: *mut leanh::LeanObject,
    mut v_ds_2924_: *mut leanh::LeanObject,
    mut v_a_2925_: *mut leanh::LeanObject,
    mut v_a_2926_: *mut leanh::LeanObject,
    mut v_a_2927_: *mut leanh::LeanObject,
    mut v_a_2928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_keep_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mask_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2939_: u8 = 0;
    let mut v_snd_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2946_: u8 = 0;
    let mut v___x_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2955_: u8 = 0;
    let mut v_isSharedCheck_2956_: u8 = 0;
    let mut v_a_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2960_: u8 = 0;
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2964_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_keep_2930_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0;
                v___x_2931_ = leanh::lean_box(0);
                v_mask_2932_ = lean_mk_array(v_nFields_2922_, v___x_2931_);
                v___x_2933_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2933_, 0, v_keep_2930_);
                leanh::lean_ctor_set(v___x_2933_, 1, v_mask_2932_);
                v___x_2934_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2934_, 0, v_ds_2924_);
                leanh::lean_ctor_set(v___x_2934_, 1, v___x_2933_);
                v___x_2935_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(v_targetId_2923_, v___x_2934_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_);
                if leanh::lean_obj_tag(v___x_2935_) == 0 {
                    v_a_2936_ = leanh::lean_ctor_get(v___x_2935_, 0);
                    v_isSharedCheck_2956_ = (!leanh::lean_is_exclusive(v___x_2935_)) as u8;
                    if v_isSharedCheck_2956_ == 0 {
                        v___x_2938_ = v___x_2935_;
                        v_isShared_2939_ = v_isSharedCheck_2956_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2936_);
                        leanh::lean_dec(v___x_2935_);
                        v___x_2938_ = leanh::lean_box(0);
                        v_isShared_2939_ = v_isSharedCheck_2956_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2957_ = leanh::lean_ctor_get(v___x_2935_, 0);
                    v_isSharedCheck_2964_ = (!leanh::lean_is_exclusive(v___x_2935_)) as u8;
                    if v_isSharedCheck_2964_ == 0 {
                        v___x_2959_ = v___x_2935_;
                        v_isShared_2960_ = v_isSharedCheck_2964_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2957_);
                        leanh::lean_dec(v___x_2935_);
                        v___x_2959_ = leanh::lean_box(0);
                        v_isShared_2960_ = v_isSharedCheck_2964_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_2940_ = leanh::lean_ctor_get(v_a_2936_, 1);
                leanh::lean_inc(v_snd_2940_);
                v_fst_2941_ = leanh::lean_ctor_get(v_a_2936_, 0);
                leanh::lean_inc(v_fst_2941_);
                leanh::lean_dec(v_a_2936_);
                v_fst_2942_ = leanh::lean_ctor_get(v_snd_2940_, 0);
                v_snd_2943_ = leanh::lean_ctor_get(v_snd_2940_, 1);
                v_isSharedCheck_2955_ = (!leanh::lean_is_exclusive(v_snd_2940_)) as u8;
                if v_isSharedCheck_2955_ == 0 {
                    v___x_2945_ = v_snd_2940_;
                    v_isShared_2946_ = v_isSharedCheck_2955_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2943_);
                    leanh::lean_inc(v_fst_2942_);
                    leanh::lean_dec(v_snd_2940_);
                    v___x_2945_ = leanh::lean_box(0);
                    v_isShared_2946_ = v_isSharedCheck_2955_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2947_ = l_Array_reverse___redArg(v_fst_2942_);
                v___x_2948_ = l_Array_append___redArg(v_fst_2941_, v___x_2947_);
                leanh::lean_dec_ref(v___x_2947_);
                if v_isShared_2946_ == 0 {
                    leanh::lean_ctor_set(v___x_2945_, 0, v___x_2948_);
                    v___x_2950_ = v___x_2945_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2954_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2948_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2954_, 1, v_snd_2943_);
                    v___x_2950_ = v_reuseFailAlloc_2954_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2939_ == 0 {
                    leanh::lean_ctor_set(v___x_2938_, 0, v___x_2950_);
                    v___x_2952_ = v___x_2938_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2953_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2953_, 0, v___x_2950_);
                    v___x_2952_ = v_reuseFailAlloc_2953_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2952_;
            }
            5 => {
                if v_isShared_2960_ == 0 {
                    v___x_2962_ = v___x_2959_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2963_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_a_2957_);
                    v___x_2962_ = v_reuseFailAlloc_2963_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2962_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___boxed(
    mut v_nFields_2965_: *mut leanh::LeanObject,
    mut v_targetId_2966_: *mut leanh::LeanObject,
    mut v_ds_2967_: *mut leanh::LeanObject,
    mut v_a_2968_: *mut leanh::LeanObject,
    mut v_a_2969_: *mut leanh::LeanObject,
    mut v_a_2970_: *mut leanh::LeanObject,
    mut v_a_2971_: *mut leanh::LeanObject,
    mut v_a_2972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2973_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(
            v_nFields_2965_,
            v_targetId_2966_,
            v_ds_2967_,
            v_a_2968_,
            v_a_2969_,
            v_a_2970_,
            v_a_2971_,
        );
    leanh::lean_dec(v_a_2971_);
    leanh::lean_dec_ref(v_a_2970_);
    leanh::lean_dec(v_a_2969_);
    leanh::lean_dec_ref(v_a_2968_);
    leanh::lean_dec(v_targetId_2966_);
    return v_res_2973_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1(
    mut v_targetId_2974_: *mut leanh::LeanObject,
    mut v_inst_2975_: *mut leanh::LeanObject,
    mut v_a_2976_: *mut leanh::LeanObject,
    mut v___y_2977_: *mut leanh::LeanObject,
    mut v___y_2978_: *mut leanh::LeanObject,
    mut v___y_2979_: *mut leanh::LeanObject,
    mut v___y_2980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2982_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(v_targetId_2974_, v_a_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_);
    return v___x_2982_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___boxed(
    mut v_targetId_2983_: *mut leanh::LeanObject,
    mut v_inst_2984_: *mut leanh::LeanObject,
    mut v_a_2985_: *mut leanh::LeanObject,
    mut v___y_2986_: *mut leanh::LeanObject,
    mut v___y_2987_: *mut leanh::LeanObject,
    mut v___y_2988_: *mut leanh::LeanObject,
    mut v___y_2989_: *mut leanh::LeanObject,
    mut v___y_2990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2991_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1(v_targetId_2983_, v_inst_2984_, v_a_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
    leanh::lean_dec(v___y_2989_);
    leanh::lean_dec_ref(v___y_2988_);
    leanh::lean_dec(v___y_2987_);
    leanh::lean_dec_ref(v___y_2986_);
    leanh::lean_dec(v_targetId_2983_);
    return v_res_2991_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(
    mut v_discr_3008_: *mut leanh::LeanObject,
    mut v_discrType_3009_: *mut leanh::LeanObject,
    mut v_resultType_3010_: *mut leanh::LeanObject,
    mut v_t_3011_: *mut leanh::LeanObject,
    mut v_e_3012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3014_ = l_Lean_Expr_getAppFn(v_discrType_3009_);
    v___x_3015_ = l_Lean_Expr_constName_x21(v___x_3014_);
    leanh::lean_dec_ref(v___x_3014_);
    v___x_3016_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__3;
    v___x_3017_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3017_, 0, v___x_3016_);
    leanh::lean_ctor_set(v___x_3017_, 1, v_e_3012_);
    v___x_3018_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__6;
    v___x_3019_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3019_, 0, v___x_3018_);
    leanh::lean_ctor_set(v___x_3019_, 1, v_t_3011_);
    v___x_3020_ = leanh::lean_unsigned_to_nat(2);
    v___x_3021_ = lean_mk_empty_array_with_capacity(v___x_3020_);
    v___x_3022_ = lean_array_push(v___x_3021_, v___x_3017_);
    v___x_3023_ = lean_array_push(v___x_3022_, v___x_3019_);
    v___x_3024_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3024_, 0, v___x_3015_);
    leanh::lean_ctor_set(v___x_3024_, 1, v_resultType_3010_);
    leanh::lean_ctor_set(v___x_3024_, 2, v_discr_3008_);
    leanh::lean_ctor_set(v___x_3024_, 3, v___x_3023_);
    v___x_3025_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3025_, 0, v___x_3024_);
    v___x_3026_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3026_, 0, v___x_3025_);
    return v___x_3026_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___boxed(
    mut v_discr_3027_: *mut leanh::LeanObject,
    mut v_discrType_3028_: *mut leanh::LeanObject,
    mut v_resultType_3029_: *mut leanh::LeanObject,
    mut v_t_3030_: *mut leanh::LeanObject,
    mut v_e_3031_: *mut leanh::LeanObject,
    mut v_a_3032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3033_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(
            v_discr_3027_,
            v_discrType_3028_,
            v_resultType_3029_,
            v_t_3030_,
            v_e_3031_,
        );
    leanh::lean_dec_ref(v_discrType_3028_);
    return v_res_3033_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf(
    mut v_discr_3034_: *mut leanh::LeanObject,
    mut v_discrType_3035_: *mut leanh::LeanObject,
    mut v_resultType_3036_: *mut leanh::LeanObject,
    mut v_t_3037_: *mut leanh::LeanObject,
    mut v_e_3038_: *mut leanh::LeanObject,
    mut v_a_3039_: *mut leanh::LeanObject,
    mut v_a_3040_: *mut leanh::LeanObject,
    mut v_a_3041_: *mut leanh::LeanObject,
    mut v_a_3042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3044_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(
            v_discr_3034_,
            v_discrType_3035_,
            v_resultType_3036_,
            v_t_3037_,
            v_e_3038_,
        );
    return v___x_3044_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___boxed(
    mut v_discr_3045_: *mut leanh::LeanObject,
    mut v_discrType_3046_: *mut leanh::LeanObject,
    mut v_resultType_3047_: *mut leanh::LeanObject,
    mut v_t_3048_: *mut leanh::LeanObject,
    mut v_e_3049_: *mut leanh::LeanObject,
    mut v_a_3050_: *mut leanh::LeanObject,
    mut v_a_3051_: *mut leanh::LeanObject,
    mut v_a_3052_: *mut leanh::LeanObject,
    mut v_a_3053_: *mut leanh::LeanObject,
    mut v_a_3054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3055_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf(
        v_discr_3045_,
        v_discrType_3046_,
        v_resultType_3047_,
        v_t_3048_,
        v_e_3049_,
        v_a_3050_,
        v_a_3051_,
        v_a_3052_,
        v_a_3053_,
    );
    leanh::lean_dec(v_a_3053_);
    leanh::lean_dec_ref(v_a_3052_);
    leanh::lean_dec(v_a_3051_);
    leanh::lean_dec_ref(v_a_3050_);
    leanh::lean_dec_ref(v_discrType_3046_);
    return v_res_3055_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__0(
    mut v_msg_3056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3057_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0);
    v___x_3058_ = lean_panic_fn_borrowed(v___x_3057_, v_msg_3056_);
    return v___x_3058_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3061_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1;
    v___x_3062_ = leanh::lean_unsigned_to_nat(11);
    v___x_3063_ = leanh::lean_unsigned_to_nat(138);
    v___x_3064_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__0;
    v___x_3065_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1;
    v___x_3066_ = l_mkPanicMessageWithDecl(
        v___x_3065_,
        v___x_3064_,
        v___x_3063_,
        v___x_3062_,
        v___x_3061_,
    );
    return v___x_3066_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(
    mut v_targetId_3067_: *mut leanh::LeanObject,
    mut v_sz_3068_: usize,
    mut v_i_3069_: usize,
    mut v_bs_3070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3071_: u8 = 0;
    let mut v_v_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: usize = 0;
    let mut v___x_3078_: usize = 0;
    let mut v___x_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3085_: u8 = 0;
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3089_: u8 = 0;
    let mut v_unused_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3097_: u8 = 0;
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3101_: u8 = 0;
    let mut v_unused_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3107_: u8 = 0;
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3111_: u8 = 0;
    let mut v_unused_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3071_ = lean_usize_dec_lt(v_i_3069_, v_sz_3068_);
                if v___x_3071_ == 0 {
                    leanh::lean_dec(v_targetId_3067_);
                    return v_bs_3070_;
                } else {
                    v_v_3072_ = lean_array_uget(v_bs_3070_, v_i_3069_);
                    v___x_3073_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3074_ = lean_array_uset(v_bs_3070_, v_i_3069_, v___x_3073_);
                    match leanh::lean_obj_tag(v_v_3072_) {
                        3 => {
                            v_i_3081_ = leanh::lean_ctor_get(v_v_3072_, 1);
                            v_y_3082_ = leanh::lean_ctor_get(v_v_3072_, 2);
                            v_isSharedCheck_3089_ =
                                (!leanh::lean_is_exclusive(v_v_3072_)) as u8;
                            if v_isSharedCheck_3089_ == 0 {
                                v_unused_3090_ = leanh::lean_ctor_get(v_v_3072_, 0);
                                leanh::lean_dec(v_unused_3090_);
                                v___x_3084_ = v_v_3072_;
                                v_isShared_3085_ = v_isSharedCheck_3089_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_y_3082_);
                                leanh::lean_inc(v_i_3081_);
                                leanh::lean_dec(v_v_3072_);
                                v___x_3084_ = leanh::lean_box(0);
                                v_isShared_3085_ = v_isSharedCheck_3089_;
                                state = 2;
                                continue;
                            }
                        }
                        5 => {
                            v_i_3091_ = leanh::lean_ctor_get(v_v_3072_, 1);
                            v_offset_3092_ = leanh::lean_ctor_get(v_v_3072_, 2);
                            v_y_3093_ = leanh::lean_ctor_get(v_v_3072_, 3);
                            v_ty_3094_ = leanh::lean_ctor_get(v_v_3072_, 4);
                            v_isSharedCheck_3101_ =
                                (!leanh::lean_is_exclusive(v_v_3072_)) as u8;
                            if v_isSharedCheck_3101_ == 0 {
                                v_unused_3102_ = leanh::lean_ctor_get(v_v_3072_, 0);
                                leanh::lean_dec(v_unused_3102_);
                                v___x_3096_ = v_v_3072_;
                                v_isShared_3097_ = v_isSharedCheck_3101_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_ty_3094_);
                                leanh::lean_inc(v_y_3093_);
                                leanh::lean_inc(v_offset_3092_);
                                leanh::lean_inc(v_i_3091_);
                                leanh::lean_dec(v_v_3072_);
                                v___x_3096_ = leanh::lean_box(0);
                                v_isShared_3097_ = v_isSharedCheck_3101_;
                                state = 4;
                                continue;
                            }
                        }
                        4 => {
                            v_i_3103_ = leanh::lean_ctor_get(v_v_3072_, 1);
                            v_y_3104_ = leanh::lean_ctor_get(v_v_3072_, 2);
                            v_isSharedCheck_3111_ =
                                (!leanh::lean_is_exclusive(v_v_3072_)) as u8;
                            if v_isSharedCheck_3111_ == 0 {
                                v_unused_3112_ = leanh::lean_ctor_get(v_v_3072_, 0);
                                leanh::lean_dec(v_unused_3112_);
                                v___x_3106_ = v_v_3072_;
                                v_isShared_3107_ = v_isSharedCheck_3111_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_y_3104_);
                                leanh::lean_inc(v_i_3103_);
                                leanh::lean_dec(v_v_3072_);
                                v___x_3106_ = leanh::lean_box(0);
                                v_isShared_3107_ = v_isSharedCheck_3111_;
                                state = 6;
                                continue;
                            }
                        }
                        _ => {
                            leanh::lean_dec(v_v_3072_);
                            v___x_3113_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2);
                            v___x_3114_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__0(v___x_3113_);
                            v___y_3076_ = v___x_3114_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3077_ = 1usize;
                v___x_3078_ = lean_usize_add(v_i_3069_, v___x_3077_);
                v___x_3079_ = lean_array_uset(v_bs_x27_3074_, v_i_3069_, v___y_3076_);
                v_i_3069_ = v___x_3078_;
                v_bs_3070_ = v___x_3079_;
                state = 0;
                continue;
            }
            2 => {
                leanh::lean_inc(v_targetId_3067_);
                if v_isShared_3085_ == 0 {
                    leanh::lean_ctor_set(v___x_3084_, 0, v_targetId_3067_);
                    v___x_3087_ = v___x_3084_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3088_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_targetId_3067_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3088_, 1, v_i_3081_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3088_, 2, v_y_3082_);
                    v___x_3087_ = v_reuseFailAlloc_3088_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_3076_ = v___x_3087_;
                state = 1;
                continue;
            }
            4 => {
                leanh::lean_inc(v_targetId_3067_);
                if v_isShared_3097_ == 0 {
                    leanh::lean_ctor_set(v___x_3096_, 0, v_targetId_3067_);
                    v___x_3099_ = v___x_3096_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3100_ = leanh::lean_alloc_ctor(5, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_targetId_3067_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3100_, 1, v_i_3091_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3100_, 2, v_offset_3092_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3100_, 3, v_y_3093_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3100_, 4, v_ty_3094_);
                    v___x_3099_ = v_reuseFailAlloc_3100_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_3076_ = v___x_3099_;
                state = 1;
                continue;
            }
            6 => {
                leanh::lean_inc(v_targetId_3067_);
                if v_isShared_3107_ == 0 {
                    leanh::lean_ctor_set(v___x_3106_, 0, v_targetId_3067_);
                    v___x_3109_ = v___x_3106_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3110_ = leanh::lean_alloc_ctor(4, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_targetId_3067_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3110_, 1, v_i_3103_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3110_, 2, v_y_3104_);
                    v___x_3109_ = v_reuseFailAlloc_3110_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3076_ = v___x_3109_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___boxed(
    mut v_targetId_3115_: *mut leanh::LeanObject,
    mut v_sz_3116_: *mut leanh::LeanObject,
    mut v_i_3117_: *mut leanh::LeanObject,
    mut v_bs_3118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3119_: usize = 0;
    let mut v_i_boxed_3120_: usize = 0;
    let mut v_res_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3119_ = leanh::lean_unbox_usize(v_sz_3116_);
    leanh::lean_dec(v_sz_3116_);
    v_i_boxed_3120_ = leanh::lean_unbox_usize(v_i_3117_);
    leanh::lean_dec(v_i_3117_);
    v_res_3121_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(v_targetId_3115_, v_sz_boxed_3119_, v_i_boxed_3120_, v_bs_3118_);
    return v_res_3121_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(
    mut v_targetId_3122_: *mut leanh::LeanObject,
    mut v_sets_3123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_3125_: usize = 0;
    let mut v___x_3126_: usize = 0;
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_3125_ = lean_array_size(v_sets_3123_);
    v___x_3126_ = 0usize;
    v___x_3127_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(v_targetId_3122_, v_sz_3125_, v___x_3126_, v_sets_3123_);
    v___x_3128_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3128_, 0, v___x_3127_);
    return v___x_3128_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg___boxed(
    mut v_targetId_3129_: *mut leanh::LeanObject,
    mut v_sets_3130_: *mut leanh::LeanObject,
    mut v_a_3131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3132_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(
            v_targetId_3129_,
            v_sets_3130_,
        );
    return v_res_3132_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets(
    mut v_targetId_3133_: *mut leanh::LeanObject,
    mut v_sets_3134_: *mut leanh::LeanObject,
    mut v_a_3135_: *mut leanh::LeanObject,
    mut v_a_3136_: *mut leanh::LeanObject,
    mut v_a_3137_: *mut leanh::LeanObject,
    mut v_a_3138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3140_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(
            v_targetId_3133_,
            v_sets_3134_,
        );
    return v___x_3140_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___boxed(
    mut v_targetId_3141_: *mut leanh::LeanObject,
    mut v_sets_3142_: *mut leanh::LeanObject,
    mut v_a_3143_: *mut leanh::LeanObject,
    mut v_a_3144_: *mut leanh::LeanObject,
    mut v_a_3145_: *mut leanh::LeanObject,
    mut v_a_3146_: *mut leanh::LeanObject,
    mut v_a_3147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3148_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets(
        v_targetId_3141_,
        v_sets_3142_,
        v_a_3143_,
        v_a_3144_,
        v_a_3145_,
        v_a_3146_,
    );
    leanh::lean_dec(v_a_3146_);
    leanh::lean_dec_ref(v_a_3145_);
    leanh::lean_dec(v_a_3144_);
    leanh::lean_dec_ref(v_a_3143_);
    return v_res_3148_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(
    mut v_fvarId_3149_: *mut leanh::LeanObject,
    mut v_i_3150_: *mut leanh::LeanObject,
    mut v_y_3151_: *mut leanh::LeanObject,
    mut v_a_3152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3154_: u8 = 0;
    let mut v___x_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: u8 = 0;
    let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3163_: u8 = 0;
    let mut v_val_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: u8 = 0;
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: u8 = 0;
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: u8 = 0;
    let mut v___x_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: u8 = 0;
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3187_: u8 = 0;
    let mut v_a_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3191_: u8 = 0;
    let mut v___x_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3195_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_y_3151_) == 0 {
                    v___x_3154_ = 0;
                    v___x_3155_ = leanh::lean_box((v___x_3154_) as usize);
                    v___x_3156_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3156_, 0, v___x_3155_);
                    return v___x_3156_;
                } else {
                    v_fvarId_3157_ = leanh::lean_ctor_get(v_y_3151_, 0);
                    v___x_3158_ = 1;
                    v___x_3159_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(
                        v___x_3158_,
                        v_fvarId_3157_,
                        v_a_3152_,
                    );
                    if leanh::lean_obj_tag(v___x_3159_) == 0 {
                        v_a_3160_ = leanh::lean_ctor_get(v___x_3159_, 0);
                        v_isSharedCheck_3187_ =
                            (!leanh::lean_is_exclusive(v___x_3159_)) as u8;
                        if v_isSharedCheck_3187_ == 0 {
                            v___x_3162_ = v___x_3159_;
                            v_isShared_3163_ = v_isSharedCheck_3187_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3160_);
                            leanh::lean_dec(v___x_3159_);
                            v___x_3162_ = leanh::lean_box(0);
                            v_isShared_3163_ = v_isSharedCheck_3187_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3188_ = leanh::lean_ctor_get(v___x_3159_, 0);
                        v_isSharedCheck_3195_ =
                            (!leanh::lean_is_exclusive(v___x_3159_)) as u8;
                        if v_isSharedCheck_3195_ == 0 {
                            v___x_3190_ = v___x_3159_;
                            v_isShared_3191_ = v_isSharedCheck_3195_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3188_);
                            leanh::lean_dec(v___x_3159_);
                            v___x_3190_ = leanh::lean_box(0);
                            v_isShared_3191_ = v_isSharedCheck_3195_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3160_) == 1 {
                    v_val_3164_ = leanh::lean_ctor_get(v_a_3160_, 0);
                    leanh::lean_inc(v_val_3164_);
                    leanh::lean_dec_ref_known(v_a_3160_, 1);
                    if leanh::lean_obj_tag(v_val_3164_) == 6 {
                        v_i_3165_ = leanh::lean_ctor_get(v_val_3164_, 0);
                        leanh::lean_inc(v_i_3165_);
                        v_var_3166_ = leanh::lean_ctor_get(v_val_3164_, 1);
                        leanh::lean_inc(v_var_3166_);
                        leanh::lean_dec_ref_known(v_val_3164_, 2);
                        v___x_3167_ = lean_nat_dec_eq(v_i_3150_, v_i_3165_);
                        leanh::lean_dec(v_i_3165_);
                        if v___x_3167_ == 0 {
                            leanh::lean_dec(v_var_3166_);
                            v___x_3168_ = leanh::lean_box((v___x_3167_) as usize);
                            if v_isShared_3163_ == 0 {
                                leanh::lean_ctor_set(v___x_3162_, 0, v___x_3168_);
                                v___x_3170_ = v___x_3162_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_3171_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3171_, 0, v___x_3168_);
                                v___x_3170_ = v_reuseFailAlloc_3171_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_3172_ = l_Lean_instBEqFVarId_beq(v_fvarId_3149_, v_var_3166_);
                            leanh::lean_dec(v_var_3166_);
                            v___x_3173_ = leanh::lean_box((v___x_3172_) as usize);
                            if v_isShared_3163_ == 0 {
                                leanh::lean_ctor_set(v___x_3162_, 0, v___x_3173_);
                                v___x_3175_ = v___x_3162_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3176_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3176_, 0, v___x_3173_);
                                v___x_3175_ = v_reuseFailAlloc_3176_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_val_3164_);
                        v___x_3177_ = 0;
                        v___x_3178_ = leanh::lean_box((v___x_3177_) as usize);
                        if v_isShared_3163_ == 0 {
                            leanh::lean_ctor_set(v___x_3162_, 0, v___x_3178_);
                            v___x_3180_ = v___x_3162_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3181_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3181_, 0, v___x_3178_);
                            v___x_3180_ = v_reuseFailAlloc_3181_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_3160_);
                    v___x_3182_ = 0;
                    v___x_3183_ = leanh::lean_box((v___x_3182_) as usize);
                    if v_isShared_3163_ == 0 {
                        leanh::lean_ctor_set(v___x_3162_, 0, v___x_3183_);
                        v___x_3185_ = v___x_3162_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3186_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3186_, 0, v___x_3183_);
                        v___x_3185_ = v_reuseFailAlloc_3186_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3170_;
            }
            3 => {
                return v___x_3175_;
            }
            4 => {
                return v___x_3180_;
            }
            5 => {
                return v___x_3185_;
            }
            6 => {
                if v_isShared_3191_ == 0 {
                    v___x_3193_ = v___x_3190_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3194_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_a_3188_);
                    v___x_3193_ = v_reuseFailAlloc_3194_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3193_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg___boxed(
    mut v_fvarId_3196_: *mut leanh::LeanObject,
    mut v_i_3197_: *mut leanh::LeanObject,
    mut v_y_3198_: *mut leanh::LeanObject,
    mut v_a_3199_: *mut leanh::LeanObject,
    mut v_a_3200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3201_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(
            v_fvarId_3196_,
            v_i_3197_,
            v_y_3198_,
            v_a_3199_,
        );
    leanh::lean_dec(v_a_3199_);
    leanh::lean_dec(v_y_3198_);
    leanh::lean_dec(v_i_3197_);
    leanh::lean_dec(v_fvarId_3196_);
    return v_res_3201_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset(
    mut v_fvarId_3202_: *mut leanh::LeanObject,
    mut v_i_3203_: *mut leanh::LeanObject,
    mut v_y_3204_: *mut leanh::LeanObject,
    mut v_a_3205_: *mut leanh::LeanObject,
    mut v_a_3206_: *mut leanh::LeanObject,
    mut v_a_3207_: *mut leanh::LeanObject,
    mut v_a_3208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3210_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(
            v_fvarId_3202_,
            v_i_3203_,
            v_y_3204_,
            v_a_3206_,
        );
    return v___x_3210_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___boxed(
    mut v_fvarId_3211_: *mut leanh::LeanObject,
    mut v_i_3212_: *mut leanh::LeanObject,
    mut v_y_3213_: *mut leanh::LeanObject,
    mut v_a_3214_: *mut leanh::LeanObject,
    mut v_a_3215_: *mut leanh::LeanObject,
    mut v_a_3216_: *mut leanh::LeanObject,
    mut v_a_3217_: *mut leanh::LeanObject,
    mut v_a_3218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3219_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset(
        v_fvarId_3211_,
        v_i_3212_,
        v_y_3213_,
        v_a_3214_,
        v_a_3215_,
        v_a_3216_,
        v_a_3217_,
    );
    leanh::lean_dec(v_a_3217_);
    leanh::lean_dec_ref(v_a_3216_);
    leanh::lean_dec(v_a_3215_);
    leanh::lean_dec_ref(v_a_3214_);
    leanh::lean_dec(v_y_3213_);
    leanh::lean_dec(v_i_3212_);
    leanh::lean_dec(v_fvarId_3211_);
    return v_res_3219_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(
    mut v_fvarId_3220_: *mut leanh::LeanObject,
    mut v_i_3221_: *mut leanh::LeanObject,
    mut v_y_3222_: *mut leanh::LeanObject,
    mut v_a_3223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3225_: u8 = 0;
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3230_: u8 = 0;
    let mut v_val_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: u8 = 0;
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: u8 = 0;
    let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: u8 = 0;
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: u8 = 0;
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3254_: u8 = 0;
    let mut v_a_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3258_: u8 = 0;
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3262_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3225_ = 1;
                v___x_3226_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(
                    v___x_3225_,
                    v_y_3222_,
                    v_a_3223_,
                );
                if leanh::lean_obj_tag(v___x_3226_) == 0 {
                    v_a_3227_ = leanh::lean_ctor_get(v___x_3226_, 0);
                    v_isSharedCheck_3254_ = (!leanh::lean_is_exclusive(v___x_3226_)) as u8;
                    if v_isSharedCheck_3254_ == 0 {
                        v___x_3229_ = v___x_3226_;
                        v_isShared_3230_ = v_isSharedCheck_3254_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3227_);
                        leanh::lean_dec(v___x_3226_);
                        v___x_3229_ = leanh::lean_box(0);
                        v_isShared_3230_ = v_isSharedCheck_3254_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3255_ = leanh::lean_ctor_get(v___x_3226_, 0);
                    v_isSharedCheck_3262_ = (!leanh::lean_is_exclusive(v___x_3226_)) as u8;
                    if v_isSharedCheck_3262_ == 0 {
                        v___x_3257_ = v___x_3226_;
                        v_isShared_3258_ = v_isSharedCheck_3262_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3255_);
                        leanh::lean_dec(v___x_3226_);
                        v___x_3257_ = leanh::lean_box(0);
                        v_isShared_3258_ = v_isSharedCheck_3262_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3227_) == 1 {
                    v_val_3231_ = leanh::lean_ctor_get(v_a_3227_, 0);
                    leanh::lean_inc(v_val_3231_);
                    leanh::lean_dec_ref_known(v_a_3227_, 1);
                    if leanh::lean_obj_tag(v_val_3231_) == 7 {
                        v_i_3232_ = leanh::lean_ctor_get(v_val_3231_, 0);
                        leanh::lean_inc(v_i_3232_);
                        v_var_3233_ = leanh::lean_ctor_get(v_val_3231_, 1);
                        leanh::lean_inc(v_var_3233_);
                        leanh::lean_dec_ref_known(v_val_3231_, 2);
                        v___x_3234_ = lean_nat_dec_eq(v_i_3221_, v_i_3232_);
                        leanh::lean_dec(v_i_3232_);
                        if v___x_3234_ == 0 {
                            leanh::lean_dec(v_var_3233_);
                            v___x_3235_ = leanh::lean_box((v___x_3234_) as usize);
                            if v_isShared_3230_ == 0 {
                                leanh::lean_ctor_set(v___x_3229_, 0, v___x_3235_);
                                v___x_3237_ = v___x_3229_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_3238_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3235_);
                                v___x_3237_ = v_reuseFailAlloc_3238_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_3239_ = l_Lean_instBEqFVarId_beq(v_fvarId_3220_, v_var_3233_);
                            leanh::lean_dec(v_var_3233_);
                            v___x_3240_ = leanh::lean_box((v___x_3239_) as usize);
                            if v_isShared_3230_ == 0 {
                                leanh::lean_ctor_set(v___x_3229_, 0, v___x_3240_);
                                v___x_3242_ = v___x_3229_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3243_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3243_, 0, v___x_3240_);
                                v___x_3242_ = v_reuseFailAlloc_3243_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_val_3231_);
                        v___x_3244_ = 0;
                        v___x_3245_ = leanh::lean_box((v___x_3244_) as usize);
                        if v_isShared_3230_ == 0 {
                            leanh::lean_ctor_set(v___x_3229_, 0, v___x_3245_);
                            v___x_3247_ = v___x_3229_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3248_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3245_);
                            v___x_3247_ = v_reuseFailAlloc_3248_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_3227_);
                    v___x_3249_ = 0;
                    v___x_3250_ = leanh::lean_box((v___x_3249_) as usize);
                    if v_isShared_3230_ == 0 {
                        leanh::lean_ctor_set(v___x_3229_, 0, v___x_3250_);
                        v___x_3252_ = v___x_3229_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3253_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3253_, 0, v___x_3250_);
                        v___x_3252_ = v_reuseFailAlloc_3253_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3237_;
            }
            3 => {
                return v___x_3242_;
            }
            4 => {
                return v___x_3247_;
            }
            5 => {
                return v___x_3252_;
            }
            6 => {
                if v_isShared_3258_ == 0 {
                    v___x_3260_ = v___x_3257_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3261_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3255_);
                    v___x_3260_ = v_reuseFailAlloc_3261_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3260_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg___boxed(
    mut v_fvarId_3263_: *mut leanh::LeanObject,
    mut v_i_3264_: *mut leanh::LeanObject,
    mut v_y_3265_: *mut leanh::LeanObject,
    mut v_a_3266_: *mut leanh::LeanObject,
    mut v_a_3267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3268_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(
            v_fvarId_3263_,
            v_i_3264_,
            v_y_3265_,
            v_a_3266_,
        );
    leanh::lean_dec(v_a_3266_);
    leanh::lean_dec(v_y_3265_);
    leanh::lean_dec(v_i_3264_);
    leanh::lean_dec(v_fvarId_3263_);
    return v_res_3268_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset(
    mut v_fvarId_3269_: *mut leanh::LeanObject,
    mut v_i_3270_: *mut leanh::LeanObject,
    mut v_y_3271_: *mut leanh::LeanObject,
    mut v_a_3272_: *mut leanh::LeanObject,
    mut v_a_3273_: *mut leanh::LeanObject,
    mut v_a_3274_: *mut leanh::LeanObject,
    mut v_a_3275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3277_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(
            v_fvarId_3269_,
            v_i_3270_,
            v_y_3271_,
            v_a_3273_,
        );
    return v___x_3277_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___boxed(
    mut v_fvarId_3278_: *mut leanh::LeanObject,
    mut v_i_3279_: *mut leanh::LeanObject,
    mut v_y_3280_: *mut leanh::LeanObject,
    mut v_a_3281_: *mut leanh::LeanObject,
    mut v_a_3282_: *mut leanh::LeanObject,
    mut v_a_3283_: *mut leanh::LeanObject,
    mut v_a_3284_: *mut leanh::LeanObject,
    mut v_a_3285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3286_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset(
        v_fvarId_3278_,
        v_i_3279_,
        v_y_3280_,
        v_a_3281_,
        v_a_3282_,
        v_a_3283_,
        v_a_3284_,
    );
    leanh::lean_dec(v_a_3284_);
    leanh::lean_dec_ref(v_a_3283_);
    leanh::lean_dec(v_a_3282_);
    leanh::lean_dec_ref(v_a_3281_);
    leanh::lean_dec(v_y_3280_);
    leanh::lean_dec(v_i_3279_);
    leanh::lean_dec(v_fvarId_3278_);
    return v_res_3286_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(
    mut v_fvarId_3287_: *mut leanh::LeanObject,
    mut v_i_3288_: *mut leanh::LeanObject,
    mut v_offset_3289_: *mut leanh::LeanObject,
    mut v_y_3290_: *mut leanh::LeanObject,
    mut v_a_3291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3293_: u8 = 0;
    let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3298_: u8 = 0;
    let mut v_val_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3304_: u8 = 0;
    let mut v___x_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: u8 = 0;
    let mut v___x_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: u8 = 0;
    let mut v___x_3315_: u8 = 0;
    let mut v___x_3316_: u8 = 0;
    let mut v___x_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: u8 = 0;
    let mut v___x_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3326_: u8 = 0;
    let mut v_a_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3330_: u8 = 0;
    let mut v___x_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3334_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3293_ = 1;
                v___x_3294_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(
                    v___x_3293_,
                    v_y_3290_,
                    v_a_3291_,
                );
                if leanh::lean_obj_tag(v___x_3294_) == 0 {
                    v_a_3295_ = leanh::lean_ctor_get(v___x_3294_, 0);
                    v_isSharedCheck_3326_ = (!leanh::lean_is_exclusive(v___x_3294_)) as u8;
                    if v_isSharedCheck_3326_ == 0 {
                        v___x_3297_ = v___x_3294_;
                        v_isShared_3298_ = v_isSharedCheck_3326_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3295_);
                        leanh::lean_dec(v___x_3294_);
                        v___x_3297_ = leanh::lean_box(0);
                        v_isShared_3298_ = v_isSharedCheck_3326_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3327_ = leanh::lean_ctor_get(v___x_3294_, 0);
                    v_isSharedCheck_3334_ = (!leanh::lean_is_exclusive(v___x_3294_)) as u8;
                    if v_isSharedCheck_3334_ == 0 {
                        v___x_3329_ = v___x_3294_;
                        v_isShared_3330_ = v_isSharedCheck_3334_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3327_);
                        leanh::lean_dec(v___x_3294_);
                        v___x_3329_ = leanh::lean_box(0);
                        v_isShared_3330_ = v_isSharedCheck_3334_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3295_) == 1 {
                    v_val_3299_ = leanh::lean_ctor_get(v_a_3295_, 0);
                    leanh::lean_inc(v_val_3299_);
                    leanh::lean_dec_ref_known(v_a_3295_, 1);
                    if leanh::lean_obj_tag(v_val_3299_) == 8 {
                        v_n_3300_ = leanh::lean_ctor_get(v_val_3299_, 0);
                        leanh::lean_inc(v_n_3300_);
                        v_offset_3301_ = leanh::lean_ctor_get(v_val_3299_, 1);
                        leanh::lean_inc(v_offset_3301_);
                        v_var_3302_ = leanh::lean_ctor_get(v_val_3299_, 2);
                        leanh::lean_inc(v_var_3302_);
                        leanh::lean_dec_ref_known(v_val_3299_, 3);
                        v___x_3314_ = lean_nat_dec_eq(v_i_3288_, v_n_3300_);
                        leanh::lean_dec(v_n_3300_);
                        if v___x_3314_ == 0 {
                            leanh::lean_dec(v_offset_3301_);
                            v___y_3304_ = v___x_3314_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3315_ = lean_nat_dec_eq(v_offset_3289_, v_offset_3301_);
                            leanh::lean_dec(v_offset_3301_);
                            v___y_3304_ = v___x_3315_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_3299_);
                        v___x_3316_ = 0;
                        v___x_3317_ = leanh::lean_box((v___x_3316_) as usize);
                        if v_isShared_3298_ == 0 {
                            leanh::lean_ctor_set(v___x_3297_, 0, v___x_3317_);
                            v___x_3319_ = v___x_3297_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3320_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3320_, 0, v___x_3317_);
                            v___x_3319_ = v_reuseFailAlloc_3320_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_3295_);
                    v___x_3321_ = 0;
                    v___x_3322_ = leanh::lean_box((v___x_3321_) as usize);
                    if v_isShared_3298_ == 0 {
                        leanh::lean_ctor_set(v___x_3297_, 0, v___x_3322_);
                        v___x_3324_ = v___x_3297_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3325_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3322_);
                        v___x_3324_ = v_reuseFailAlloc_3325_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v___y_3304_ == 0 {
                    leanh::lean_dec(v_var_3302_);
                    v___x_3305_ = leanh::lean_box((v___y_3304_) as usize);
                    if v_isShared_3298_ == 0 {
                        leanh::lean_ctor_set(v___x_3297_, 0, v___x_3305_);
                        v___x_3307_ = v___x_3297_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3308_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3308_, 0, v___x_3305_);
                        v___x_3307_ = v_reuseFailAlloc_3308_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_3309_ = l_Lean_instBEqFVarId_beq(v_fvarId_3287_, v_var_3302_);
                    leanh::lean_dec(v_var_3302_);
                    v___x_3310_ = leanh::lean_box((v___x_3309_) as usize);
                    if v_isShared_3298_ == 0 {
                        leanh::lean_ctor_set(v___x_3297_, 0, v___x_3310_);
                        v___x_3312_ = v___x_3297_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3313_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3310_);
                        v___x_3312_ = v_reuseFailAlloc_3313_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3307_;
            }
            4 => {
                return v___x_3312_;
            }
            5 => {
                return v___x_3319_;
            }
            6 => {
                return v___x_3324_;
            }
            7 => {
                if v_isShared_3330_ == 0 {
                    v___x_3332_ = v___x_3329_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3333_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_a_3327_);
                    v___x_3332_ = v_reuseFailAlloc_3333_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3332_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg___boxed(
    mut v_fvarId_3335_: *mut leanh::LeanObject,
    mut v_i_3336_: *mut leanh::LeanObject,
    mut v_offset_3337_: *mut leanh::LeanObject,
    mut v_y_3338_: *mut leanh::LeanObject,
    mut v_a_3339_: *mut leanh::LeanObject,
    mut v_a_3340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3341_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(
            v_fvarId_3335_,
            v_i_3336_,
            v_offset_3337_,
            v_y_3338_,
            v_a_3339_,
        );
    leanh::lean_dec(v_a_3339_);
    leanh::lean_dec(v_y_3338_);
    leanh::lean_dec(v_offset_3337_);
    leanh::lean_dec(v_i_3336_);
    leanh::lean_dec(v_fvarId_3335_);
    return v_res_3341_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset(
    mut v_fvarId_3342_: *mut leanh::LeanObject,
    mut v_i_3343_: *mut leanh::LeanObject,
    mut v_offset_3344_: *mut leanh::LeanObject,
    mut v_y_3345_: *mut leanh::LeanObject,
    mut v_a_3346_: *mut leanh::LeanObject,
    mut v_a_3347_: *mut leanh::LeanObject,
    mut v_a_3348_: *mut leanh::LeanObject,
    mut v_a_3349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3351_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(
            v_fvarId_3342_,
            v_i_3343_,
            v_offset_3344_,
            v_y_3345_,
            v_a_3347_,
        );
    return v___x_3351_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___boxed(
    mut v_fvarId_3352_: *mut leanh::LeanObject,
    mut v_i_3353_: *mut leanh::LeanObject,
    mut v_offset_3354_: *mut leanh::LeanObject,
    mut v_y_3355_: *mut leanh::LeanObject,
    mut v_a_3356_: *mut leanh::LeanObject,
    mut v_a_3357_: *mut leanh::LeanObject,
    mut v_a_3358_: *mut leanh::LeanObject,
    mut v_a_3359_: *mut leanh::LeanObject,
    mut v_a_3360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3361_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset(
        v_fvarId_3352_,
        v_i_3353_,
        v_offset_3354_,
        v_y_3355_,
        v_a_3356_,
        v_a_3357_,
        v_a_3358_,
        v_a_3359_,
    );
    leanh::lean_dec(v_a_3359_);
    leanh::lean_dec_ref(v_a_3358_);
    leanh::lean_dec(v_a_3357_);
    leanh::lean_dec_ref(v_a_3356_);
    leanh::lean_dec(v_y_3355_);
    leanh::lean_dec(v_offset_3354_);
    leanh::lean_dec(v_i_3353_);
    leanh::lean_dec(v_fvarId_3352_);
    return v_res_3361_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(
    mut v_msg_3362_: *mut leanh::LeanObject,
    mut v___y_3363_: *mut leanh::LeanObject,
    mut v___y_3364_: *mut leanh::LeanObject,
    mut v___y_3365_: *mut leanh::LeanObject,
    mut v___y_3366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3373_: u8 = 0;
    let mut v_toFunctor_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3380_: u8 = 0;
    let mut v___f_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: u8 = 0;
    let mut v___x_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994__overap_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3402_: u8 = 0;
    let mut v_unused_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3404_: u8 = 0;
    let mut v_unused_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3368_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0);
                v___x_3369_ = l_StateRefT_x27_instMonad___redArg(v___x_3368_);
                v_toApplicative_3370_ = leanh::lean_ctor_get(v___x_3369_, 0);
                v_isSharedCheck_3404_ = (!leanh::lean_is_exclusive(v___x_3369_)) as u8;
                if v_isSharedCheck_3404_ == 0 {
                    v_unused_3405_ = leanh::lean_ctor_get(v___x_3369_, 1);
                    leanh::lean_dec(v_unused_3405_);
                    v___x_3372_ = v___x_3369_;
                    v_isShared_3373_ = v_isSharedCheck_3404_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_3370_);
                    leanh::lean_dec(v___x_3369_);
                    v___x_3372_ = leanh::lean_box(0);
                    v_isShared_3373_ = v_isSharedCheck_3404_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3374_ = leanh::lean_ctor_get(v_toApplicative_3370_, 0);
                v_toSeq_3375_ = leanh::lean_ctor_get(v_toApplicative_3370_, 2);
                v_toSeqLeft_3376_ = leanh::lean_ctor_get(v_toApplicative_3370_, 3);
                v_toSeqRight_3377_ = leanh::lean_ctor_get(v_toApplicative_3370_, 4);
                v_isSharedCheck_3402_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_3370_)) as u8;
                if v_isSharedCheck_3402_ == 0 {
                    v_unused_3403_ = leanh::lean_ctor_get(v_toApplicative_3370_, 1);
                    leanh::lean_dec(v_unused_3403_);
                    v___x_3379_ = v_toApplicative_3370_;
                    v_isShared_3380_ = v_isSharedCheck_3402_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_3377_);
                    leanh::lean_inc(v_toSeqLeft_3376_);
                    leanh::lean_inc(v_toSeq_3375_);
                    leanh::lean_inc(v_toFunctor_3374_);
                    leanh::lean_dec(v_toApplicative_3370_);
                    v___x_3379_ = leanh::lean_box(0);
                    v_isShared_3380_ = v_isSharedCheck_3402_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_3381_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1;
                v___f_3382_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2;
                leanh::lean_inc_ref(v_toFunctor_3374_);
                v___f_3383_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3383_, 0, v_toFunctor_3374_);
                v___f_3384_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3384_, 0, v_toFunctor_3374_);
                v___x_3385_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3385_, 0, v___f_3383_);
                leanh::lean_ctor_set(v___x_3385_, 1, v___f_3384_);
                v___f_3386_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3386_, 0, v_toSeqRight_3377_);
                v___f_3387_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3387_, 0, v_toSeqLeft_3376_);
                v___f_3388_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3388_, 0, v_toSeq_3375_);
                if v_isShared_3380_ == 0 {
                    leanh::lean_ctor_set(v___x_3379_, 4, v___f_3386_);
                    leanh::lean_ctor_set(v___x_3379_, 3, v___f_3387_);
                    leanh::lean_ctor_set(v___x_3379_, 2, v___f_3388_);
                    leanh::lean_ctor_set(v___x_3379_, 1, v___f_3381_);
                    leanh::lean_ctor_set(v___x_3379_, 0, v___x_3385_);
                    v___x_3390_ = v___x_3379_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3401_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3401_, 0, v___x_3385_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3401_, 1, v___f_3381_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3401_, 2, v___f_3388_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3401_, 3, v___f_3387_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3401_, 4, v___f_3386_);
                    v___x_3390_ = v_reuseFailAlloc_3401_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3373_ == 0 {
                    leanh::lean_ctor_set(v___x_3372_, 1, v___f_3382_);
                    leanh::lean_ctor_set(v___x_3372_, 0, v___x_3390_);
                    v___x_3392_ = v___x_3372_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3400_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3400_, 0, v___x_3390_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3400_, 1, v___f_3382_);
                    v___x_3392_ = v_reuseFailAlloc_3400_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3393_ = l_StateRefT_x27_instMonad___redArg(v___x_3392_);
                v___x_3394_ = 0;
                v___x_3395_ = leanh::lean_box((v___x_3394_) as usize);
                v___x_3396_ = l_instInhabitedOfMonad___redArg(v___x_3393_, v___x_3395_);
                v___f_3397_ = leanh::lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_3397_, 0, v___x_3396_);
                v___x_994__overap_3398_ = lean_panic_fn_borrowed(v___f_3397_, v_msg_3362_);
                leanh::lean_dec_ref(v___f_3397_);
                leanh::lean_inc(v___y_3366_);
                leanh::lean_inc_ref(v___y_3365_);
                leanh::lean_inc(v___y_3364_);
                leanh::lean_inc_ref(v___y_3363_);
                v___x_3399_ = leanh::lean_apply_5(
                    v___x_994__overap_3398_,
                    v___y_3363_,
                    v___y_3364_,
                    v___y_3365_,
                    v___y_3366_,
                    leanh::lean_box(0),
                );
                return v___x_3399_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0___boxed(
    mut v_msg_3406_: *mut leanh::LeanObject,
    mut v___y_3407_: *mut leanh::LeanObject,
    mut v___y_3408_: *mut leanh::LeanObject,
    mut v___y_3409_: *mut leanh::LeanObject,
    mut v___y_3410_: *mut leanh::LeanObject,
    mut v___y_3411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3412_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(v_msg_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
    leanh::lean_dec(v___y_3410_);
    leanh::lean_dec_ref(v___y_3409_);
    leanh::lean_dec(v___y_3408_);
    leanh::lean_dec_ref(v___y_3407_);
    return v_res_3412_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3414_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1;
    v___x_3415_ = leanh::lean_unsigned_to_nat(13);
    v___x_3416_ = leanh::lean_unsigned_to_nat(174);
    v___x_3417_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__0;
    v___x_3418_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1;
    v___x_3419_ = l_mkPanicMessageWithDecl(
        v___x_3418_,
        v___x_3417_,
        v___x_3416_,
        v___x_3415_,
        v___x_3414_,
    );
    return v___x_3419_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(
    mut v_selfId_3420_: *mut leanh::LeanObject,
    mut v_as_3421_: *mut leanh::LeanObject,
    mut v_sz_3422_: usize,
    mut v_i_3423_: usize,
    mut v_b_3424_: *mut leanh::LeanObject,
    mut v___y_3425_: *mut leanh::LeanObject,
    mut v___y_3426_: *mut leanh::LeanObject,
    mut v___y_3427_: *mut leanh::LeanObject,
    mut v___y_3428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: usize = 0;
    let mut v___x_3433_: usize = 0;
    let mut v___x_3435_: u8 = 0;
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3441_: u8 = 0;
    let mut v_a_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: u8 = 0;
    let mut v___x_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3458_: u8 = 0;
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3462_: u8 = 0;
    let mut v_i_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3475_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3435_ = lean_usize_dec_lt(v_i_3423_, v_sz_3422_);
                if v___x_3435_ == 0 {
                    v___x_3436_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3436_, 0, v_b_3424_);
                    return v___x_3436_;
                } else {
                    v_fst_3437_ = leanh::lean_ctor_get(v_b_3424_, 0);
                    v_snd_3438_ = leanh::lean_ctor_get(v_b_3424_, 1);
                    v_isSharedCheck_3475_ = (!leanh::lean_is_exclusive(v_b_3424_)) as u8;
                    if v_isSharedCheck_3475_ == 0 {
                        v___x_3440_ = v_b_3424_;
                        v_isShared_3441_ = v_isSharedCheck_3475_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3438_);
                        leanh::lean_inc(v_fst_3437_);
                        leanh::lean_dec(v_b_3424_);
                        v___x_3440_ = leanh::lean_box(0);
                        v_isShared_3441_ = v_isSharedCheck_3475_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3432_ = 1usize;
                v___x_3433_ = lean_usize_add(v_i_3423_, v___x_3432_);
                v_i_3423_ = v___x_3433_;
                v_b_3424_ = v_a_3431_;
                state = 0;
                continue;
            }
            2 => {
                v_a_3442_ = lean_array_uget_borrowed(v_as_3421_, v_i_3423_);
                match leanh::lean_obj_tag(v_a_3442_) {
                    3 => {
                        v_i_3463_ = leanh::lean_ctor_get(v_a_3442_, 1);
                        v_y_3464_ = leanh::lean_ctor_get(v_a_3442_, 2);
                        v___x_3465_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_selfId_3420_, v_i_3463_, v_y_3464_, v___y_3426_);
                        v___y_3444_ = v___x_3465_;
                        state = 3;
                        continue;
                    }
                    4 => {
                        v_i_3466_ = leanh::lean_ctor_get(v_a_3442_, 1);
                        v_y_3467_ = leanh::lean_ctor_get(v_a_3442_, 2);
                        v___x_3468_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(v_selfId_3420_, v_i_3466_, v_y_3467_, v___y_3426_);
                        v___y_3444_ = v___x_3468_;
                        state = 3;
                        continue;
                    }
                    5 => {
                        v_i_3469_ = leanh::lean_ctor_get(v_a_3442_, 1);
                        v_offset_3470_ = leanh::lean_ctor_get(v_a_3442_, 2);
                        v_y_3471_ = leanh::lean_ctor_get(v_a_3442_, 3);
                        v___x_3472_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(v_selfId_3420_, v_i_3469_, v_offset_3470_, v_y_3471_, v___y_3426_);
                        v___y_3444_ = v___x_3472_;
                        state = 3;
                        continue;
                    }
                    _ => {
                        v___x_3473_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1);
                        v___x_3474_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(v___x_3473_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
                        v___y_3444_ = v___x_3474_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if leanh::lean_obj_tag(v___y_3444_) == 0 {
                    v_a_3445_ = leanh::lean_ctor_get(v___y_3444_, 0);
                    leanh::lean_inc(v_a_3445_);
                    leanh::lean_dec_ref_known(v___y_3444_, 1);
                    v___x_3446_ = (leanh::lean_unbox(v_a_3445_) as u8);
                    leanh::lean_dec(v_a_3445_);
                    if v___x_3446_ == 0 {
                        leanh::lean_inc(v_a_3442_);
                        v___x_3447_ = lean_array_push(v_fst_3437_, v_a_3442_);
                        if v_isShared_3441_ == 0 {
                            leanh::lean_ctor_set(v___x_3440_, 0, v___x_3447_);
                            v___x_3449_ = v___x_3440_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3450_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3450_, 0, v___x_3447_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3450_, 1, v_snd_3438_);
                            v___x_3449_ = v_reuseFailAlloc_3450_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_a_3442_);
                        v___x_3451_ = lean_array_push(v_snd_3438_, v_a_3442_);
                        if v_isShared_3441_ == 0 {
                            leanh::lean_ctor_set(v___x_3440_, 1, v___x_3451_);
                            v___x_3453_ = v___x_3440_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3454_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_fst_3437_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3454_, 1, v___x_3451_);
                            v___x_3453_ = v_reuseFailAlloc_3454_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_3440_);
                    leanh::lean_dec(v_snd_3438_);
                    leanh::lean_dec(v_fst_3437_);
                    v_a_3455_ = leanh::lean_ctor_get(v___y_3444_, 0);
                    v_isSharedCheck_3462_ = (!leanh::lean_is_exclusive(v___y_3444_)) as u8;
                    if v_isSharedCheck_3462_ == 0 {
                        v___x_3457_ = v___y_3444_;
                        v_isShared_3458_ = v_isSharedCheck_3462_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3455_);
                        leanh::lean_dec(v___y_3444_);
                        v___x_3457_ = leanh::lean_box(0);
                        v_isShared_3458_ = v_isSharedCheck_3462_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v_a_3431_ = v___x_3449_;
                state = 1;
                continue;
            }
            5 => {
                v_a_3431_ = v___x_3453_;
                state = 1;
                continue;
            }
            6 => {
                if v_isShared_3458_ == 0 {
                    v___x_3460_ = v___x_3457_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3461_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_a_3455_);
                    v___x_3460_ = v_reuseFailAlloc_3461_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3460_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___boxed(
    mut v_selfId_3476_: *mut leanh::LeanObject,
    mut v_as_3477_: *mut leanh::LeanObject,
    mut v_sz_3478_: *mut leanh::LeanObject,
    mut v_i_3479_: *mut leanh::LeanObject,
    mut v_b_3480_: *mut leanh::LeanObject,
    mut v___y_3481_: *mut leanh::LeanObject,
    mut v___y_3482_: *mut leanh::LeanObject,
    mut v___y_3483_: *mut leanh::LeanObject,
    mut v___y_3484_: *mut leanh::LeanObject,
    mut v___y_3485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3486_: usize = 0;
    let mut v_i_boxed_3487_: usize = 0;
    let mut v_res_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3486_ = leanh::lean_unbox_usize(v_sz_3478_);
    leanh::lean_dec(v_sz_3478_);
    v_i_boxed_3487_ = leanh::lean_unbox_usize(v_i_3479_);
    leanh::lean_dec(v_i_3479_);
    v_res_3488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(v_selfId_3476_, v_as_3477_, v_sz_boxed_3486_, v_i_boxed_3487_, v_b_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
    leanh::lean_dec(v___y_3484_);
    leanh::lean_dec_ref(v___y_3483_);
    leanh::lean_dec(v___y_3482_);
    leanh::lean_dec_ref(v___y_3481_);
    leanh::lean_dec_ref(v_as_3477_);
    leanh::lean_dec(v_selfId_3476_);
    return v_res_3488_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(
    mut v_selfId_3491_: *mut leanh::LeanObject,
    mut v_sets_3492_: *mut leanh::LeanObject,
    mut v_a_3493_: *mut leanh::LeanObject,
    mut v_a_3494_: *mut leanh::LeanObject,
    mut v_a_3495_: *mut leanh::LeanObject,
    mut v_a_3496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3499_: usize = 0;
    let mut v___x_3500_: usize = 0;
    let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3505_: u8 = 0;
    let mut v_fst_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3510_: u8 = 0;
    let mut v___x_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3517_: u8 = 0;
    let mut v_isSharedCheck_3518_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3498_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___closed__0;
                v_sz_3499_ = lean_array_size(v_sets_3492_);
                v___x_3500_ = 0usize;
                v___x_3501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(v_selfId_3491_, v_sets_3492_, v_sz_3499_, v___x_3500_, v___x_3498_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_);
                if leanh::lean_obj_tag(v___x_3501_) == 0 {
                    v_a_3502_ = leanh::lean_ctor_get(v___x_3501_, 0);
                    v_isSharedCheck_3518_ = (!leanh::lean_is_exclusive(v___x_3501_)) as u8;
                    if v_isSharedCheck_3518_ == 0 {
                        v___x_3504_ = v___x_3501_;
                        v_isShared_3505_ = v_isSharedCheck_3518_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3502_);
                        leanh::lean_dec(v___x_3501_);
                        v___x_3504_ = leanh::lean_box(0);
                        v_isShared_3505_ = v_isSharedCheck_3518_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_3501_;
                }
            }
            1 => {
                v_fst_3506_ = leanh::lean_ctor_get(v_a_3502_, 0);
                v_snd_3507_ = leanh::lean_ctor_get(v_a_3502_, 1);
                v_isSharedCheck_3517_ = (!leanh::lean_is_exclusive(v_a_3502_)) as u8;
                if v_isSharedCheck_3517_ == 0 {
                    v___x_3509_ = v_a_3502_;
                    v_isShared_3510_ = v_isSharedCheck_3517_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3507_);
                    leanh::lean_inc(v_fst_3506_);
                    leanh::lean_dec(v_a_3502_);
                    v___x_3509_ = leanh::lean_box(0);
                    v_isShared_3510_ = v_isSharedCheck_3517_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_3510_ == 0 {
                    leanh::lean_ctor_set(v___x_3509_, 1, v_fst_3506_);
                    leanh::lean_ctor_set(v___x_3509_, 0, v_snd_3507_);
                    v___x_3512_ = v___x_3509_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3516_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_snd_3507_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3516_, 1, v_fst_3506_);
                    v___x_3512_ = v_reuseFailAlloc_3516_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3505_ == 0 {
                    leanh::lean_ctor_set(v___x_3504_, 0, v___x_3512_);
                    v___x_3514_ = v___x_3504_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3515_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3515_, 0, v___x_3512_);
                    v___x_3514_ = v_reuseFailAlloc_3515_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3514_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___boxed(
    mut v_selfId_3519_: *mut leanh::LeanObject,
    mut v_sets_3520_: *mut leanh::LeanObject,
    mut v_a_3521_: *mut leanh::LeanObject,
    mut v_a_3522_: *mut leanh::LeanObject,
    mut v_a_3523_: *mut leanh::LeanObject,
    mut v_a_3524_: *mut leanh::LeanObject,
    mut v_a_3525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3526_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(
            v_selfId_3519_,
            v_sets_3520_,
            v_a_3521_,
            v_a_3522_,
            v_a_3523_,
            v_a_3524_,
        );
    leanh::lean_dec(v_a_3524_);
    leanh::lean_dec_ref(v_a_3523_);
    leanh::lean_dec(v_a_3522_);
    leanh::lean_dec_ref(v_a_3521_);
    leanh::lean_dec_ref(v_sets_3520_);
    leanh::lean_dec(v_selfId_3519_);
    return v_res_3526_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(
    mut v_target_3527_: *mut leanh::LeanObject,
    mut v_a_3528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3534_: u8 = 0;
    let mut v_fvarId_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: u8 = 0;
    let mut v___x_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: u8 = 0;
    let mut v___x_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3549_: u8 = 0;
    let mut v_unused_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3554_: u8 = 0;
    let mut v_fvarId_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: u8 = 0;
    let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: u8 = 0;
    let mut v___x_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3569_: u8 = 0;
    let mut v_unused_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3574_: u8 = 0;
    let mut v_fvarId_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: u8 = 0;
    let mut v___x_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: u8 = 0;
    let mut v___x_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3589_: u8 = 0;
    let mut v_unused_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3594_: u8 = 0;
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3599_: u8 = 0;
    let mut v_unused_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_3530_ = leanh::lean_ctor_get(v_a_3528_, 1);
                leanh::lean_inc(v_snd_3530_);
                match leanh::lean_obj_tag(v_snd_3530_) {
                    7 => {
                        v_fst_3531_ = leanh::lean_ctor_get(v_a_3528_, 0);
                        v_isSharedCheck_3549_ = (!leanh::lean_is_exclusive(v_a_3528_)) as u8;
                        if v_isSharedCheck_3549_ == 0 {
                            v_unused_3550_ = leanh::lean_ctor_get(v_a_3528_, 1);
                            leanh::lean_dec(v_unused_3550_);
                            v___x_3533_ = v_a_3528_;
                            v_isShared_3534_ = v_isSharedCheck_3549_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_fst_3531_);
                            leanh::lean_dec(v_a_3528_);
                            v___x_3533_ = leanh::lean_box(0);
                            v_isShared_3534_ = v_isSharedCheck_3549_;
                            state = 1;
                            continue;
                        }
                    }
                    9 => {
                        v_fst_3551_ = leanh::lean_ctor_get(v_a_3528_, 0);
                        v_isSharedCheck_3569_ = (!leanh::lean_is_exclusive(v_a_3528_)) as u8;
                        if v_isSharedCheck_3569_ == 0 {
                            v_unused_3570_ = leanh::lean_ctor_get(v_a_3528_, 1);
                            leanh::lean_dec(v_unused_3570_);
                            v___x_3553_ = v_a_3528_;
                            v_isShared_3554_ = v_isSharedCheck_3569_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_fst_3551_);
                            leanh::lean_dec(v_a_3528_);
                            v___x_3553_ = leanh::lean_box(0);
                            v_isShared_3554_ = v_isSharedCheck_3569_;
                            state = 4;
                            continue;
                        }
                    }
                    8 => {
                        v_fst_3571_ = leanh::lean_ctor_get(v_a_3528_, 0);
                        v_isSharedCheck_3589_ = (!leanh::lean_is_exclusive(v_a_3528_)) as u8;
                        if v_isSharedCheck_3589_ == 0 {
                            v_unused_3590_ = leanh::lean_ctor_get(v_a_3528_, 1);
                            leanh::lean_dec(v_unused_3590_);
                            v___x_3573_ = v_a_3528_;
                            v_isShared_3574_ = v_isSharedCheck_3589_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_fst_3571_);
                            leanh::lean_dec(v_a_3528_);
                            v___x_3573_ = leanh::lean_box(0);
                            v_isShared_3574_ = v_isSharedCheck_3589_;
                            state = 7;
                            continue;
                        }
                    }
                    _ => {
                        v_fst_3591_ = leanh::lean_ctor_get(v_a_3528_, 0);
                        v_isSharedCheck_3599_ = (!leanh::lean_is_exclusive(v_a_3528_)) as u8;
                        if v_isSharedCheck_3599_ == 0 {
                            v_unused_3600_ = leanh::lean_ctor_get(v_a_3528_, 1);
                            leanh::lean_dec(v_unused_3600_);
                            v___x_3593_ = v_a_3528_;
                            v_isShared_3594_ = v_isSharedCheck_3599_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_fst_3591_);
                            leanh::lean_dec(v_a_3528_);
                            v___x_3593_ = leanh::lean_box(0);
                            v_isShared_3594_ = v_isSharedCheck_3599_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fvarId_3535_ = leanh::lean_ctor_get(v_snd_3530_, 0);
                v_k_3536_ = leanh::lean_ctor_get(v_snd_3530_, 3);
                v___x_3537_ = l_Lean_instBEqFVarId_beq(v_target_3527_, v_fvarId_3535_);
                if v___x_3537_ == 0 {
                    if v_isShared_3534_ == 0 {
                        v___x_3539_ = v___x_3533_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3541_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_fst_3531_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3541_, 1, v_snd_3530_);
                        v___x_3539_ = v_reuseFailAlloc_3541_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_k_3536_);
                    v___x_3542_ = 1;
                    v___x_3543_ =
                        l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_3542_, v_snd_3530_);
                    leanh::lean_dec_ref_known(v_snd_3530_, 4);
                    v___x_3544_ = lean_array_push(v_fst_3531_, v___x_3543_);
                    if v_isShared_3534_ == 0 {
                        leanh::lean_ctor_set(v___x_3533_, 1, v_k_3536_);
                        leanh::lean_ctor_set(v___x_3533_, 0, v___x_3544_);
                        v___x_3546_ = v___x_3533_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3548_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3544_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3548_, 1, v_k_3536_);
                        v___x_3546_ = v_reuseFailAlloc_3548_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3540_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3540_, 0, v___x_3539_);
                return v___x_3540_;
            }
            3 => {
                v_a_3528_ = v___x_3546_;
                state = 0;
                continue;
            }
            4 => {
                v_fvarId_3555_ = leanh::lean_ctor_get(v_snd_3530_, 0);
                v_k_3556_ = leanh::lean_ctor_get(v_snd_3530_, 5);
                v___x_3557_ = l_Lean_instBEqFVarId_beq(v_target_3527_, v_fvarId_3555_);
                if v___x_3557_ == 0 {
                    if v_isShared_3554_ == 0 {
                        v___x_3559_ = v___x_3553_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3561_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_fst_3551_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3561_, 1, v_snd_3530_);
                        v___x_3559_ = v_reuseFailAlloc_3561_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_k_3556_);
                    v___x_3562_ = 1;
                    v___x_3563_ =
                        l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_3562_, v_snd_3530_);
                    leanh::lean_dec_ref_known(v_snd_3530_, 6);
                    v___x_3564_ = lean_array_push(v_fst_3551_, v___x_3563_);
                    if v_isShared_3554_ == 0 {
                        leanh::lean_ctor_set(v___x_3553_, 1, v_k_3556_);
                        leanh::lean_ctor_set(v___x_3553_, 0, v___x_3564_);
                        v___x_3566_ = v___x_3553_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3568_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3568_, 0, v___x_3564_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3568_, 1, v_k_3556_);
                        v___x_3566_ = v_reuseFailAlloc_3568_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                v___x_3560_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3560_, 0, v___x_3559_);
                return v___x_3560_;
            }
            6 => {
                v_a_3528_ = v___x_3566_;
                state = 0;
                continue;
            }
            7 => {
                v_fvarId_3575_ = leanh::lean_ctor_get(v_snd_3530_, 0);
                v_k_3576_ = leanh::lean_ctor_get(v_snd_3530_, 3);
                v___x_3577_ = l_Lean_instBEqFVarId_beq(v_target_3527_, v_fvarId_3575_);
                if v___x_3577_ == 0 {
                    if v_isShared_3574_ == 0 {
                        v___x_3579_ = v___x_3573_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3581_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_fst_3571_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3581_, 1, v_snd_3530_);
                        v___x_3579_ = v_reuseFailAlloc_3581_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_k_3576_);
                    v___x_3582_ = 1;
                    v___x_3583_ =
                        l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_3582_, v_snd_3530_);
                    leanh::lean_dec_ref_known(v_snd_3530_, 4);
                    v___x_3584_ = lean_array_push(v_fst_3571_, v___x_3583_);
                    if v_isShared_3574_ == 0 {
                        leanh::lean_ctor_set(v___x_3573_, 1, v_k_3576_);
                        leanh::lean_ctor_set(v___x_3573_, 0, v___x_3584_);
                        v___x_3586_ = v___x_3573_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3588_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3584_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3588_, 1, v_k_3576_);
                        v___x_3586_ = v_reuseFailAlloc_3588_;
                        state = 9;
                        continue;
                    }
                }
            }
            8 => {
                v___x_3580_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3580_, 0, v___x_3579_);
                return v___x_3580_;
            }
            9 => {
                v_a_3528_ = v___x_3586_;
                state = 0;
                continue;
            }
            10 => {
                if v_isShared_3594_ == 0 {
                    v___x_3596_ = v___x_3593_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3598_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_fst_3591_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3598_, 1, v_snd_3530_);
                    v___x_3596_ = v_reuseFailAlloc_3598_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_3597_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3597_, 0, v___x_3596_);
                return v___x_3597_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg___boxed(
    mut v_target_3601_: *mut leanh::LeanObject,
    mut v_a_3602_: *mut leanh::LeanObject,
    mut v___y_3603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3604_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_3601_, v_a_3602_);
    leanh::lean_dec(v_target_3601_);
    return v_res_3604_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(
    mut v_target_3605_: *mut leanh::LeanObject,
    mut v_k_3606_: *mut leanh::LeanObject,
    mut v_a_3607_: *mut leanh::LeanObject,
    mut v_a_3608_: *mut leanh::LeanObject,
    mut v_a_3609_: *mut leanh::LeanObject,
    mut v_a_3610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sets_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3618_: u8 = 0;
    let mut v_fst_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3623_: u8 = 0;
    let mut v___x_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3630_: u8 = 0;
    let mut v_isSharedCheck_3631_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sets_3612_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0;
                v___x_3613_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3613_, 0, v_sets_3612_);
                leanh::lean_ctor_set(v___x_3613_, 1, v_k_3606_);
                v___x_3614_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_3605_, v___x_3613_);
                if leanh::lean_obj_tag(v___x_3614_) == 0 {
                    v_a_3615_ = leanh::lean_ctor_get(v___x_3614_, 0);
                    v_isSharedCheck_3631_ = (!leanh::lean_is_exclusive(v___x_3614_)) as u8;
                    if v_isSharedCheck_3631_ == 0 {
                        v___x_3617_ = v___x_3614_;
                        v_isShared_3618_ = v_isSharedCheck_3631_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3615_);
                        leanh::lean_dec(v___x_3614_);
                        v___x_3617_ = leanh::lean_box(0);
                        v_isShared_3618_ = v_isSharedCheck_3631_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_3614_;
                }
            }
            1 => {
                v_fst_3619_ = leanh::lean_ctor_get(v_a_3615_, 0);
                v_snd_3620_ = leanh::lean_ctor_get(v_a_3615_, 1);
                v_isSharedCheck_3630_ = (!leanh::lean_is_exclusive(v_a_3615_)) as u8;
                if v_isSharedCheck_3630_ == 0 {
                    v___x_3622_ = v_a_3615_;
                    v_isShared_3623_ = v_isSharedCheck_3630_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3620_);
                    leanh::lean_inc(v_fst_3619_);
                    leanh::lean_dec(v_a_3615_);
                    v___x_3622_ = leanh::lean_box(0);
                    v_isShared_3623_ = v_isSharedCheck_3630_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_3623_ == 0 {
                    v___x_3625_ = v___x_3622_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3629_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_fst_3619_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3629_, 1, v_snd_3620_);
                    v___x_3625_ = v_reuseFailAlloc_3629_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3618_ == 0 {
                    leanh::lean_ctor_set(v___x_3617_, 0, v___x_3625_);
                    v___x_3627_ = v___x_3617_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3628_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3628_, 0, v___x_3625_);
                    v___x_3627_ = v_reuseFailAlloc_3628_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3627_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets___boxed(
    mut v_target_3632_: *mut leanh::LeanObject,
    mut v_k_3633_: *mut leanh::LeanObject,
    mut v_a_3634_: *mut leanh::LeanObject,
    mut v_a_3635_: *mut leanh::LeanObject,
    mut v_a_3636_: *mut leanh::LeanObject,
    mut v_a_3637_: *mut leanh::LeanObject,
    mut v_a_3638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3639_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(
            v_target_3632_,
            v_k_3633_,
            v_a_3634_,
            v_a_3635_,
            v_a_3636_,
            v_a_3637_,
        );
    leanh::lean_dec(v_a_3637_);
    leanh::lean_dec_ref(v_a_3636_);
    leanh::lean_dec(v_a_3635_);
    leanh::lean_dec_ref(v_a_3634_);
    leanh::lean_dec(v_target_3632_);
    return v_res_3639_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0(
    mut v_target_3640_: *mut leanh::LeanObject,
    mut v_inst_3641_: *mut leanh::LeanObject,
    mut v_a_3642_: *mut leanh::LeanObject,
    mut v___y_3643_: *mut leanh::LeanObject,
    mut v___y_3644_: *mut leanh::LeanObject,
    mut v___y_3645_: *mut leanh::LeanObject,
    mut v___y_3646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3648_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_3640_, v_a_3642_);
    return v___x_3648_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___boxed(
    mut v_target_3649_: *mut leanh::LeanObject,
    mut v_inst_3650_: *mut leanh::LeanObject,
    mut v_a_3651_: *mut leanh::LeanObject,
    mut v___y_3652_: *mut leanh::LeanObject,
    mut v___y_3653_: *mut leanh::LeanObject,
    mut v___y_3654_: *mut leanh::LeanObject,
    mut v___y_3655_: *mut leanh::LeanObject,
    mut v___y_3656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3657_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0(v_target_3649_, v_inst_3650_, v_a_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_);
    leanh::lean_dec(v___y_3655_);
    leanh::lean_dec_ref(v___y_3654_);
    leanh::lean_dec(v___y_3653_);
    leanh::lean_dec_ref(v___y_3652_);
    leanh::lean_dec(v_target_3649_);
    return v_res_3657_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3664_ = leanh::lean_box(0);
    v___x_3665_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__3;
    v___x_3666_ = l_Lean_Expr_const___override(v___x_3665_, v___x_3664_);
    return v___x_3666_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(
    mut v_upperBound_3667_: *mut leanh::LeanObject,
    mut v_mask_3668_: *mut leanh::LeanObject,
    mut v_origAllocId_3669_: *mut leanh::LeanObject,
    mut v_a_3670_: *mut leanh::LeanObject,
    mut v_b_3671_: *mut leanh::LeanObject,
    mut v___y_3672_: *mut leanh::LeanObject,
    mut v___y_3673_: *mut leanh::LeanObject,
    mut v___y_3674_: *mut leanh::LeanObject,
    mut v___y_3675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: u8 = 0;
    let mut v___x_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: u8 = 0;
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: u8 = 0;
    let mut v___x_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3702_: u8 = 0;
    let mut v___x_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3706_: u8 = 0;
    let mut v_a_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3710_: u8 = 0;
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3714_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3682_ = lean_nat_dec_lt(v_a_3670_, v_upperBound_3667_);
                if v___x_3682_ == 0 {
                    leanh::lean_dec(v_a_3670_);
                    leanh::lean_dec(v_origAllocId_3669_);
                    v___x_3683_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3683_, 0, v_b_3671_);
                    return v___x_3683_;
                } else {
                    v___x_3684_ = lean_array_fget_borrowed(v_mask_3668_, v_a_3670_);
                    if leanh::lean_obj_tag(v___x_3684_) == 0 {
                        v___x_3685_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__1;
                        v___x_3686_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(
                            v___x_3685_,
                            v___y_3673_,
                        );
                        if leanh::lean_obj_tag(v___x_3686_) == 0 {
                            v_a_3687_ = leanh::lean_ctor_get(v___x_3686_, 0);
                            leanh::lean_inc(v_a_3687_);
                            leanh::lean_dec_ref_known(v___x_3686_, 1);
                            v___x_3688_ = 1;
                            v___x_3689_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4);
                            leanh::lean_inc(v_origAllocId_3669_);
                            leanh::lean_inc(v_a_3670_);
                            v___x_3690_ = leanh::lean_alloc_ctor(6, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3690_, 0, v_a_3670_);
                            leanh::lean_ctor_set(v___x_3690_, 1, v_origAllocId_3669_);
                            v___x_3691_ = l_Lean_Compiler_LCNF_mkLetDecl(
                                v___x_3688_,
                                v_a_3687_,
                                v___x_3689_,
                                v___x_3690_,
                                v___y_3672_,
                                v___y_3673_,
                                v___y_3674_,
                                v___y_3675_,
                            );
                            if leanh::lean_obj_tag(v___x_3691_) == 0 {
                                v_a_3692_ = leanh::lean_ctor_get(v___x_3691_, 0);
                                leanh::lean_inc(v_a_3692_);
                                leanh::lean_dec_ref_known(v___x_3691_, 1);
                                v_fvarId_3693_ = leanh::lean_ctor_get(v_a_3692_, 0);
                                v___x_3694_ = 0;
                                v___x_3695_ = leanh::lean_unsigned_to_nat(1);
                                v___x_3696_ = leanh::lean_box(0);
                                leanh::lean_inc(v_fvarId_3693_);
                                v___x_3697_ = leanh::lean_alloc_ctor(12, 4, (2) as u32);
                                leanh::lean_ctor_set(v___x_3697_, 0, v_fvarId_3693_);
                                leanh::lean_ctor_set(v___x_3697_, 1, v___x_3695_);
                                leanh::lean_ctor_set(v___x_3697_, 2, v___x_3696_);
                                leanh::lean_ctor_set(v___x_3697_, 3, v_b_3671_);
                                leanh::lean_ctor_set_uint8(
                                    v___x_3697_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4)
                                        as u32,
                                    v___x_3682_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v___x_3697_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1)
                                        as u32,
                                    v___x_3694_,
                                );
                                v___x_3698_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3698_, 0, v_a_3692_);
                                leanh::lean_ctor_set(v___x_3698_, 1, v___x_3697_);
                                v_a_3678_ = v___x_3698_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_b_3671_);
                                leanh::lean_dec(v_a_3670_);
                                leanh::lean_dec(v_origAllocId_3669_);
                                v_a_3699_ = leanh::lean_ctor_get(v___x_3691_, 0);
                                v_isSharedCheck_3706_ =
                                    (!leanh::lean_is_exclusive(v___x_3691_)) as u8;
                                if v_isSharedCheck_3706_ == 0 {
                                    v___x_3701_ = v___x_3691_;
                                    v_isShared_3702_ = v_isSharedCheck_3706_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3699_);
                                    leanh::lean_dec(v___x_3691_);
                                    v___x_3701_ = leanh::lean_box(0);
                                    v_isShared_3702_ = v_isSharedCheck_3706_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_b_3671_);
                            leanh::lean_dec(v_a_3670_);
                            leanh::lean_dec(v_origAllocId_3669_);
                            v_a_3707_ = leanh::lean_ctor_get(v___x_3686_, 0);
                            v_isSharedCheck_3714_ =
                                (!leanh::lean_is_exclusive(v___x_3686_)) as u8;
                            if v_isSharedCheck_3714_ == 0 {
                                v___x_3709_ = v___x_3686_;
                                v_isShared_3710_ = v_isSharedCheck_3714_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3707_);
                                leanh::lean_dec(v___x_3686_);
                                v___x_3709_ = leanh::lean_box(0);
                                v_isShared_3710_ = v_isSharedCheck_3714_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_a_3678_ = v_b_3671_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3679_ = leanh::lean_unsigned_to_nat(1);
                v___x_3680_ = lean_nat_add(v_a_3670_, v___x_3679_);
                leanh::lean_dec(v_a_3670_);
                v_a_3670_ = v___x_3680_;
                v_b_3671_ = v_a_3678_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_3702_ == 0 {
                    v___x_3704_ = v___x_3701_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3705_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3699_);
                    v___x_3704_ = v_reuseFailAlloc_3705_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3704_;
            }
            4 => {
                if v_isShared_3710_ == 0 {
                    v___x_3712_ = v___x_3709_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3713_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_a_3707_);
                    v___x_3712_ = v_reuseFailAlloc_3713_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3712_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___boxed(
    mut v_upperBound_3715_: *mut leanh::LeanObject,
    mut v_mask_3716_: *mut leanh::LeanObject,
    mut v_origAllocId_3717_: *mut leanh::LeanObject,
    mut v_a_3718_: *mut leanh::LeanObject,
    mut v_b_3719_: *mut leanh::LeanObject,
    mut v___y_3720_: *mut leanh::LeanObject,
    mut v___y_3721_: *mut leanh::LeanObject,
    mut v___y_3722_: *mut leanh::LeanObject,
    mut v___y_3723_: *mut leanh::LeanObject,
    mut v___y_3724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3725_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v_upperBound_3715_, v_mask_3716_, v_origAllocId_3717_, v_a_3718_, v_b_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
    leanh::lean_dec(v___y_3723_);
    leanh::lean_dec_ref(v___y_3722_);
    leanh::lean_dec(v___y_3721_);
    leanh::lean_dec_ref(v___y_3720_);
    leanh::lean_dec_ref(v_mask_3716_);
    leanh::lean_dec(v_upperBound_3715_);
    return v_res_3725_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(
    mut v_origAllocId_3726_: *mut leanh::LeanObject,
    mut v_mask_3727_: *mut leanh::LeanObject,
    mut v_resetJpId_3728_: *mut leanh::LeanObject,
    mut v_isSharedId_3729_: *mut leanh::LeanObject,
    mut v_a_3730_: *mut leanh::LeanObject,
    mut v_a_3731_: *mut leanh::LeanObject,
    mut v_a_3732_: *mut leanh::LeanObject,
    mut v_a_3733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_origAllocId_3726_);
    v___x_3735_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3735_, 0, v_origAllocId_3726_);
    v___x_3736_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3736_, 0, v_isSharedId_3729_);
    v___x_3737_ = leanh::lean_unsigned_to_nat(0);
    v___x_3738_ = lean_array_get_size(v_mask_3727_);
    v___x_3739_ = leanh::lean_unsigned_to_nat(2);
    v___x_3740_ = lean_mk_empty_array_with_capacity(v___x_3739_);
    v___x_3741_ = lean_array_push(v___x_3740_, v___x_3735_);
    v___x_3742_ = lean_array_push(v___x_3741_, v___x_3736_);
    v_code_3743_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v_code_3743_, 0, v_resetJpId_3728_);
    leanh::lean_ctor_set(v_code_3743_, 1, v___x_3742_);
    v___x_3744_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v___x_3738_, v_mask_3727_, v_origAllocId_3726_, v___x_3737_, v_code_3743_, v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_);
    return v___x_3744_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath___boxed(
    mut v_origAllocId_3745_: *mut leanh::LeanObject,
    mut v_mask_3746_: *mut leanh::LeanObject,
    mut v_resetJpId_3747_: *mut leanh::LeanObject,
    mut v_isSharedId_3748_: *mut leanh::LeanObject,
    mut v_a_3749_: *mut leanh::LeanObject,
    mut v_a_3750_: *mut leanh::LeanObject,
    mut v_a_3751_: *mut leanh::LeanObject,
    mut v_a_3752_: *mut leanh::LeanObject,
    mut v_a_3753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3754_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(v_origAllocId_3745_, v_mask_3746_, v_resetJpId_3747_, v_isSharedId_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
    leanh::lean_dec(v_a_3752_);
    leanh::lean_dec_ref(v_a_3751_);
    leanh::lean_dec(v_a_3750_);
    leanh::lean_dec_ref(v_a_3749_);
    leanh::lean_dec_ref(v_mask_3746_);
    return v_res_3754_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0(
    mut v_upperBound_3755_: *mut leanh::LeanObject,
    mut v_mask_3756_: *mut leanh::LeanObject,
    mut v_origAllocId_3757_: *mut leanh::LeanObject,
    mut v_inst_3758_: *mut leanh::LeanObject,
    mut v_R_3759_: *mut leanh::LeanObject,
    mut v_a_3760_: *mut leanh::LeanObject,
    mut v_b_3761_: *mut leanh::LeanObject,
    mut v_c_3762_: *mut leanh::LeanObject,
    mut v___y_3763_: *mut leanh::LeanObject,
    mut v___y_3764_: *mut leanh::LeanObject,
    mut v___y_3765_: *mut leanh::LeanObject,
    mut v___y_3766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3768_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v_upperBound_3755_, v_mask_3756_, v_origAllocId_3757_, v_a_3760_, v_b_3761_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
    return v___x_3768_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___boxed(
    mut v_upperBound_3769_: *mut leanh::LeanObject,
    mut v_mask_3770_: *mut leanh::LeanObject,
    mut v_origAllocId_3771_: *mut leanh::LeanObject,
    mut v_inst_3772_: *mut leanh::LeanObject,
    mut v_R_3773_: *mut leanh::LeanObject,
    mut v_a_3774_: *mut leanh::LeanObject,
    mut v_b_3775_: *mut leanh::LeanObject,
    mut v_c_3776_: *mut leanh::LeanObject,
    mut v___y_3777_: *mut leanh::LeanObject,
    mut v___y_3778_: *mut leanh::LeanObject,
    mut v___y_3779_: *mut leanh::LeanObject,
    mut v___y_3780_: *mut leanh::LeanObject,
    mut v___y_3781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3782_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0(v_upperBound_3769_, v_mask_3770_, v_origAllocId_3771_, v_inst_3772_, v_R_3773_, v_a_3774_, v_b_3775_, v_c_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
    leanh::lean_dec(v___y_3780_);
    leanh::lean_dec_ref(v___y_3779_);
    leanh::lean_dec(v___y_3778_);
    leanh::lean_dec_ref(v___y_3777_);
    leanh::lean_dec_ref(v_mask_3770_);
    leanh::lean_dec(v_upperBound_3769_);
    return v_res_3782_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(
    mut v_as_3783_: *mut leanh::LeanObject,
    mut v_sz_3784_: usize,
    mut v_i_3785_: usize,
    mut v_b_3786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: usize = 0;
    let mut v___x_3791_: usize = 0;
    let mut v___x_3793_: u8 = 0;
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: u8 = 0;
    let mut v___x_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3793_ = lean_usize_dec_lt(v_i_3785_, v_sz_3784_);
                if v___x_3793_ == 0 {
                    v___x_3794_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3794_, 0, v_b_3786_);
                    return v___x_3794_;
                } else {
                    v_a_3795_ = lean_array_uget_borrowed(v_as_3783_, v_i_3785_);
                    if leanh::lean_obj_tag(v_a_3795_) == 1 {
                        v_val_3796_ = leanh::lean_ctor_get(v_a_3795_, 0);
                        v___x_3797_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3798_ = 0;
                        leanh::lean_inc(v_val_3796_);
                        v___x_3799_ = leanh::lean_alloc_ctor(11, 3, (2) as u32);
                        leanh::lean_ctor_set(v___x_3799_, 0, v_val_3796_);
                        leanh::lean_ctor_set(v___x_3799_, 1, v___x_3797_);
                        leanh::lean_ctor_set(v___x_3799_, 2, v_b_3786_);
                        leanh::lean_ctor_set_uint8(
                            v___x_3799_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                            v___x_3793_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_3799_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                            v___x_3798_,
                        );
                        v_a_3789_ = v___x_3799_;
                        state = 1;
                        continue;
                    } else {
                        v_a_3789_ = v_b_3786_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3790_ = 1usize;
                v___x_3791_ = lean_usize_add(v_i_3785_, v___x_3790_);
                v_i_3785_ = v___x_3791_;
                v_b_3786_ = v_a_3789_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg___boxed(
    mut v_as_3800_: *mut leanh::LeanObject,
    mut v_sz_3801_: *mut leanh::LeanObject,
    mut v_i_3802_: *mut leanh::LeanObject,
    mut v_b_3803_: *mut leanh::LeanObject,
    mut v___y_3804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3805_: usize = 0;
    let mut v_i_boxed_3806_: usize = 0;
    let mut v_res_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3805_ = leanh::lean_unbox_usize(v_sz_3801_);
    leanh::lean_dec(v_sz_3801_);
    v_i_boxed_3806_ = leanh::lean_unbox_usize(v_i_3802_);
    leanh::lean_dec(v_i_3802_);
    v_res_3807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(v_as_3800_, v_sz_boxed_3805_, v_i_boxed_3806_, v_b_3803_);
    leanh::lean_dec_ref(v_as_3800_);
    return v_res_3807_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3808_ = leanh::lean_box(0);
    v___x_3809_ = leanh::lean_unsigned_to_nat(2);
    v___x_3810_ = lean_mk_empty_array_with_capacity(v___x_3809_);
    v___x_3811_ = lean_array_push(v___x_3810_, v___x_3808_);
    return v___x_3811_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(
    mut v_origAllocId_3812_: *mut leanh::LeanObject,
    mut v_mask_3813_: *mut leanh::LeanObject,
    mut v_resetJpId_3814_: *mut leanh::LeanObject,
    mut v_isSharedId_3815_: *mut leanh::LeanObject,
    mut v_a_3816_: *mut leanh::LeanObject,
    mut v_a_3817_: *mut leanh::LeanObject,
    mut v_a_3818_: *mut leanh::LeanObject,
    mut v_a_3819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: u8 = 0;
    let mut v___x_3827_: u8 = 0;
    let mut v___x_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3830_: usize = 0;
    let mut v___x_3831_: usize = 0;
    let mut v___x_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3821_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3821_, 0, v_isSharedId_3815_);
    v___x_3822_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0_once), _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0);
    v___x_3823_ = lean_array_push(v___x_3822_, v___x_3821_);
    v_code_3824_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v_code_3824_, 0, v_resetJpId_3814_);
    leanh::lean_ctor_set(v_code_3824_, 1, v___x_3823_);
    v___x_3825_ = leanh::lean_unsigned_to_nat(1);
    v___x_3826_ = 1;
    v___x_3827_ = 0;
    v___x_3828_ = leanh::lean_box(0);
    v_code_3829_ = leanh::lean_alloc_ctor(12, 4, (2) as u32);
    leanh::lean_ctor_set(v_code_3829_, 0, v_origAllocId_3812_);
    leanh::lean_ctor_set(v_code_3829_, 1, v___x_3825_);
    leanh::lean_ctor_set(v_code_3829_, 2, v___x_3828_);
    leanh::lean_ctor_set(v_code_3829_, 3, v_code_3824_);
    leanh::lean_ctor_set_uint8(
        v_code_3829_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
        v___x_3826_,
    );
    leanh::lean_ctor_set_uint8(
        v_code_3829_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
        v___x_3827_,
    );
    v_sz_3830_ = lean_array_size(v_mask_3813_);
    v___x_3831_ = 0usize;
    v___x_3832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(v_mask_3813_, v_sz_3830_, v___x_3831_, v_code_3829_);
    return v___x_3832_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___boxed(
    mut v_origAllocId_3833_: *mut leanh::LeanObject,
    mut v_mask_3834_: *mut leanh::LeanObject,
    mut v_resetJpId_3835_: *mut leanh::LeanObject,
    mut v_isSharedId_3836_: *mut leanh::LeanObject,
    mut v_a_3837_: *mut leanh::LeanObject,
    mut v_a_3838_: *mut leanh::LeanObject,
    mut v_a_3839_: *mut leanh::LeanObject,
    mut v_a_3840_: *mut leanh::LeanObject,
    mut v_a_3841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3842_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(v_origAllocId_3833_, v_mask_3834_, v_resetJpId_3835_, v_isSharedId_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_);
    leanh::lean_dec(v_a_3840_);
    leanh::lean_dec_ref(v_a_3839_);
    leanh::lean_dec(v_a_3838_);
    leanh::lean_dec_ref(v_a_3837_);
    leanh::lean_dec_ref(v_mask_3834_);
    return v_res_3842_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0(
    mut v_as_3843_: *mut leanh::LeanObject,
    mut v_sz_3844_: usize,
    mut v_i_3845_: usize,
    mut v_b_3846_: *mut leanh::LeanObject,
    mut v___y_3847_: *mut leanh::LeanObject,
    mut v___y_3848_: *mut leanh::LeanObject,
    mut v___y_3849_: *mut leanh::LeanObject,
    mut v___y_3850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(v_as_3843_, v_sz_3844_, v_i_3845_, v_b_3846_);
    return v___x_3852_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___boxed(
    mut v_as_3853_: *mut leanh::LeanObject,
    mut v_sz_3854_: *mut leanh::LeanObject,
    mut v_i_3855_: *mut leanh::LeanObject,
    mut v_b_3856_: *mut leanh::LeanObject,
    mut v___y_3857_: *mut leanh::LeanObject,
    mut v___y_3858_: *mut leanh::LeanObject,
    mut v___y_3859_: *mut leanh::LeanObject,
    mut v___y_3860_: *mut leanh::LeanObject,
    mut v___y_3861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3862_: usize = 0;
    let mut v_i_boxed_3863_: usize = 0;
    let mut v_res_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3862_ = leanh::lean_unbox_usize(v_sz_3854_);
    leanh::lean_dec(v_sz_3854_);
    v_i_boxed_3863_ = leanh::lean_unbox_usize(v_i_3855_);
    leanh::lean_dec(v_i_3855_);
    v_res_3864_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0(v_as_3853_, v_sz_boxed_3862_, v_i_boxed_3863_, v_b_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
    leanh::lean_dec(v___y_3860_);
    leanh::lean_dec_ref(v___y_3859_);
    leanh::lean_dec(v___y_3858_);
    leanh::lean_dec_ref(v___y_3857_);
    leanh::lean_dec_ref(v_as_3853_);
    return v_res_3864_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(
    mut v_upperBound_3865_: *mut leanh::LeanObject,
    mut v_args_3866_: *mut leanh::LeanObject,
    mut v_origAllocId_3867_: *mut leanh::LeanObject,
    mut v_resetTokenId_3868_: *mut leanh::LeanObject,
    mut v_a_3869_: *mut leanh::LeanObject,
    mut v_b_3870_: *mut leanh::LeanObject,
    mut v___y_3871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3873_: u8 = 0;
    let mut v___x_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: u8 = 0;
    let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3888_: u8 = 0;
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3892_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3873_ = lean_nat_dec_lt(v_a_3869_, v_upperBound_3865_);
                if v___x_3873_ == 0 {
                    leanh::lean_dec(v_a_3869_);
                    leanh::lean_dec(v_resetTokenId_3868_);
                    v___x_3874_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3874_, 0, v_b_3870_);
                    return v___x_3874_;
                } else {
                    v___x_3875_ = lean_array_fget_borrowed(v_args_3866_, v_a_3869_);
                    v___x_3876_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_origAllocId_3867_, v_a_3869_, v___x_3875_, v___y_3871_);
                    if leanh::lean_obj_tag(v___x_3876_) == 0 {
                        v_a_3877_ = leanh::lean_ctor_get(v___x_3876_, 0);
                        leanh::lean_inc(v_a_3877_);
                        leanh::lean_dec_ref_known(v___x_3876_, 1);
                        v___x_3883_ = (leanh::lean_unbox(v_a_3877_) as u8);
                        leanh::lean_dec(v_a_3877_);
                        if v___x_3883_ == 0 {
                            leanh::lean_inc(v___x_3875_);
                            leanh::lean_inc(v_a_3869_);
                            leanh::lean_inc(v_resetTokenId_3868_);
                            v___x_3884_ = leanh::lean_alloc_ctor(7, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_3884_, 0, v_resetTokenId_3868_);
                            leanh::lean_ctor_set(v___x_3884_, 1, v_a_3869_);
                            leanh::lean_ctor_set(v___x_3884_, 2, v___x_3875_);
                            leanh::lean_ctor_set(v___x_3884_, 3, v_b_3870_);
                            v_a_3879_ = v___x_3884_;
                            state = 1;
                            continue;
                        } else {
                            v_a_3879_ = v_b_3870_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_3870_);
                        leanh::lean_dec(v_a_3869_);
                        leanh::lean_dec(v_resetTokenId_3868_);
                        v_a_3885_ = leanh::lean_ctor_get(v___x_3876_, 0);
                        v_isSharedCheck_3892_ =
                            (!leanh::lean_is_exclusive(v___x_3876_)) as u8;
                        if v_isSharedCheck_3892_ == 0 {
                            v___x_3887_ = v___x_3876_;
                            v_isShared_3888_ = v_isSharedCheck_3892_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3885_);
                            leanh::lean_dec(v___x_3876_);
                            v___x_3887_ = leanh::lean_box(0);
                            v_isShared_3888_ = v_isSharedCheck_3892_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3880_ = leanh::lean_unsigned_to_nat(1);
                v___x_3881_ = lean_nat_add(v_a_3869_, v___x_3880_);
                leanh::lean_dec(v_a_3869_);
                v_a_3869_ = v___x_3881_;
                v_b_3870_ = v_a_3879_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_3888_ == 0 {
                    v___x_3890_ = v___x_3887_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3891_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_a_3885_);
                    v___x_3890_ = v_reuseFailAlloc_3891_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3890_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg___boxed(
    mut v_upperBound_3893_: *mut leanh::LeanObject,
    mut v_args_3894_: *mut leanh::LeanObject,
    mut v_origAllocId_3895_: *mut leanh::LeanObject,
    mut v_resetTokenId_3896_: *mut leanh::LeanObject,
    mut v_a_3897_: *mut leanh::LeanObject,
    mut v_b_3898_: *mut leanh::LeanObject,
    mut v___y_3899_: *mut leanh::LeanObject,
    mut v___y_3900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3901_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(v_upperBound_3893_, v_args_3894_, v_origAllocId_3895_, v_resetTokenId_3896_, v_a_3897_, v_b_3898_, v___y_3899_);
    leanh::lean_dec(v___y_3899_);
    leanh::lean_dec(v_origAllocId_3895_);
    leanh::lean_dec_ref(v_args_3894_);
    leanh::lean_dec(v_upperBound_3893_);
    return v_res_3901_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(
    mut v_resetTokenId_3902_: *mut leanh::LeanObject,
    mut v_info_3903_: *mut leanh::LeanObject,
    mut v_update_3904_: u8,
    mut v_args_3905_: *mut leanh::LeanObject,
    mut v_contJpId_3906_: *mut leanh::LeanObject,
    mut v_origAllocId_3907_: *mut leanh::LeanObject,
    mut v_a_3908_: *mut leanh::LeanObject,
    mut v_a_3909_: *mut leanh::LeanObject,
    mut v_a_3910_: *mut leanh::LeanObject,
    mut v_a_3911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3924_: u8 = 0;
    let mut v_cidx_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3930_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_n(v_resetTokenId_3902_, 2);
                v___x_3913_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3913_, 0, v_resetTokenId_3902_);
                v___x_3914_ = leanh::lean_unsigned_to_nat(0);
                v___x_3915_ = lean_array_get_size(v_args_3905_);
                v___x_3916_ = leanh::lean_unsigned_to_nat(1);
                v___x_3917_ = lean_mk_empty_array_with_capacity(v___x_3916_);
                v___x_3918_ = lean_array_push(v___x_3917_, v___x_3913_);
                v_code_3919_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                leanh::lean_ctor_set(v_code_3919_, 0, v_contJpId_3906_);
                leanh::lean_ctor_set(v_code_3919_, 1, v___x_3918_);
                v___x_3920_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(v___x_3915_, v_args_3905_, v_origAllocId_3907_, v_resetTokenId_3902_, v___x_3914_, v_code_3919_, v_a_3909_);
                if leanh::lean_obj_tag(v___x_3920_) == 0 {
                    if v_update_3904_ == 0 {
                        leanh::lean_dec(v_resetTokenId_3902_);
                        return v___x_3920_;
                    } else {
                        v_a_3921_ = leanh::lean_ctor_get(v___x_3920_, 0);
                        v_isSharedCheck_3930_ =
                            (!leanh::lean_is_exclusive(v___x_3920_)) as u8;
                        if v_isSharedCheck_3930_ == 0 {
                            v___x_3923_ = v___x_3920_;
                            v_isShared_3924_ = v_isSharedCheck_3930_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3921_);
                            leanh::lean_dec(v___x_3920_);
                            v___x_3923_ = leanh::lean_box(0);
                            v_isShared_3924_ = v_isSharedCheck_3930_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_resetTokenId_3902_);
                    return v___x_3920_;
                }
            }
            1 => {
                v_cidx_3925_ = leanh::lean_ctor_get(v_info_3903_, 1);
                leanh::lean_inc(v_cidx_3925_);
                v___x_3926_ = leanh::lean_alloc_ctor(10, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3926_, 0, v_resetTokenId_3902_);
                leanh::lean_ctor_set(v___x_3926_, 1, v_cidx_3925_);
                leanh::lean_ctor_set(v___x_3926_, 2, v_a_3921_);
                if v_isShared_3924_ == 0 {
                    leanh::lean_ctor_set(v___x_3923_, 0, v___x_3926_);
                    v___x_3928_ = v___x_3923_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3929_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3929_, 0, v___x_3926_);
                    v___x_3928_ = v_reuseFailAlloc_3929_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3928_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath___boxed(
    mut v_resetTokenId_3931_: *mut leanh::LeanObject,
    mut v_info_3932_: *mut leanh::LeanObject,
    mut v_update_3933_: *mut leanh::LeanObject,
    mut v_args_3934_: *mut leanh::LeanObject,
    mut v_contJpId_3935_: *mut leanh::LeanObject,
    mut v_origAllocId_3936_: *mut leanh::LeanObject,
    mut v_a_3937_: *mut leanh::LeanObject,
    mut v_a_3938_: *mut leanh::LeanObject,
    mut v_a_3939_: *mut leanh::LeanObject,
    mut v_a_3940_: *mut leanh::LeanObject,
    mut v_a_3941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_update_boxed_3942_: u8 = 0;
    let mut v_res_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_update_boxed_3942_ = (leanh::lean_unbox(v_update_3933_) as u8);
    v_res_3943_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(v_resetTokenId_3931_, v_info_3932_, v_update_boxed_3942_, v_args_3934_, v_contJpId_3935_, v_origAllocId_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_);
    leanh::lean_dec(v_a_3940_);
    leanh::lean_dec_ref(v_a_3939_);
    leanh::lean_dec(v_a_3938_);
    leanh::lean_dec_ref(v_a_3937_);
    leanh::lean_dec(v_origAllocId_3936_);
    leanh::lean_dec_ref(v_args_3934_);
    leanh::lean_dec_ref(v_info_3932_);
    return v_res_3943_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0(
    mut v_upperBound_3944_: *mut leanh::LeanObject,
    mut v_args_3945_: *mut leanh::LeanObject,
    mut v_origAllocId_3946_: *mut leanh::LeanObject,
    mut v_resetTokenId_3947_: *mut leanh::LeanObject,
    mut v_inst_3948_: *mut leanh::LeanObject,
    mut v_R_3949_: *mut leanh::LeanObject,
    mut v_a_3950_: *mut leanh::LeanObject,
    mut v_b_3951_: *mut leanh::LeanObject,
    mut v_c_3952_: *mut leanh::LeanObject,
    mut v___y_3953_: *mut leanh::LeanObject,
    mut v___y_3954_: *mut leanh::LeanObject,
    mut v___y_3955_: *mut leanh::LeanObject,
    mut v___y_3956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3958_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(v_upperBound_3944_, v_args_3945_, v_origAllocId_3946_, v_resetTokenId_3947_, v_a_3950_, v_b_3951_, v___y_3954_);
    return v___x_3958_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___boxed(
    mut v_upperBound_3959_: *mut leanh::LeanObject,
    mut v_args_3960_: *mut leanh::LeanObject,
    mut v_origAllocId_3961_: *mut leanh::LeanObject,
    mut v_resetTokenId_3962_: *mut leanh::LeanObject,
    mut v_inst_3963_: *mut leanh::LeanObject,
    mut v_R_3964_: *mut leanh::LeanObject,
    mut v_a_3965_: *mut leanh::LeanObject,
    mut v_b_3966_: *mut leanh::LeanObject,
    mut v_c_3967_: *mut leanh::LeanObject,
    mut v___y_3968_: *mut leanh::LeanObject,
    mut v___y_3969_: *mut leanh::LeanObject,
    mut v___y_3970_: *mut leanh::LeanObject,
    mut v___y_3971_: *mut leanh::LeanObject,
    mut v___y_3972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3973_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0(v_upperBound_3959_, v_args_3960_, v_origAllocId_3961_, v_resetTokenId_3962_, v_inst_3963_, v_R_3964_, v_a_3965_, v_b_3966_, v_c_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_);
    leanh::lean_dec(v___y_3971_);
    leanh::lean_dec_ref(v___y_3970_);
    leanh::lean_dec(v___y_3969_);
    leanh::lean_dec_ref(v___y_3968_);
    leanh::lean_dec(v_origAllocId_3961_);
    leanh::lean_dec_ref(v_args_3960_);
    leanh::lean_dec(v_upperBound_3959_);
    return v_res_3973_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(
    mut v_decl_3977_: *mut leanh::LeanObject,
    mut v_info_3978_: *mut leanh::LeanObject,
    mut v_args_3979_: *mut leanh::LeanObject,
    mut v_contJpId_3980_: *mut leanh::LeanObject,
    mut v_selfSets_3981_: *mut leanh::LeanObject,
    mut v_a_3982_: *mut leanh::LeanObject,
    mut v_a_3983_: *mut leanh::LeanObject,
    mut v_a_3984_: *mut leanh::LeanObject,
    mut v_a_3985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: u8 = 0;
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4001_: u8 = 0;
    let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4011_: u8 = 0;
    let mut v_a_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4015_: u8 = 0;
    let mut v___x_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4019_: u8 = 0;
    let mut v_a_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4023_: u8 = 0;
    let mut v___x_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4027_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3987_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__1;
                v___x_3988_ =
                    l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_3987_, v_a_3983_);
                if leanh::lean_obj_tag(v___x_3988_) == 0 {
                    v_a_3989_ = leanh::lean_ctor_get(v___x_3988_, 0);
                    leanh::lean_inc(v_a_3989_);
                    leanh::lean_dec_ref_known(v___x_3988_, 1);
                    v_type_3990_ = leanh::lean_ctor_get(v_decl_3977_, 2);
                    leanh::lean_inc_ref(v_type_3990_);
                    leanh::lean_dec_ref(v_decl_3977_);
                    v___x_3991_ = 1;
                    v___x_3992_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3992_, 0, v_info_3978_);
                    leanh::lean_ctor_set(v___x_3992_, 1, v_args_3979_);
                    v___x_3993_ = l_Lean_Compiler_LCNF_mkLetDecl(
                        v___x_3991_,
                        v_a_3989_,
                        v_type_3990_,
                        v___x_3992_,
                        v_a_3982_,
                        v_a_3983_,
                        v_a_3984_,
                        v_a_3985_,
                    );
                    if leanh::lean_obj_tag(v___x_3993_) == 0 {
                        v_a_3994_ = leanh::lean_ctor_get(v___x_3993_, 0);
                        leanh::lean_inc(v_a_3994_);
                        leanh::lean_dec_ref_known(v___x_3993_, 1);
                        v_fvarId_3995_ = leanh::lean_ctor_get(v_a_3994_, 0);
                        leanh::lean_inc_n(v_fvarId_3995_, 2);
                        v___x_3996_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3996_, 0, v_fvarId_3995_);
                        v___x_3997_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(v_fvarId_3995_, v_selfSets_3981_);
                        v_a_3998_ = leanh::lean_ctor_get(v___x_3997_, 0);
                        v_isSharedCheck_4011_ =
                            (!leanh::lean_is_exclusive(v___x_3997_)) as u8;
                        if v_isSharedCheck_4011_ == 0 {
                            v___x_4000_ = v___x_3997_;
                            v_isShared_4001_ = v_isSharedCheck_4011_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3998_);
                            leanh::lean_dec(v___x_3997_);
                            v___x_4000_ = leanh::lean_box(0);
                            v_isShared_4001_ = v_isSharedCheck_4011_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_selfSets_3981_);
                        leanh::lean_dec(v_contJpId_3980_);
                        v_a_4012_ = leanh::lean_ctor_get(v___x_3993_, 0);
                        v_isSharedCheck_4019_ =
                            (!leanh::lean_is_exclusive(v___x_3993_)) as u8;
                        if v_isSharedCheck_4019_ == 0 {
                            v___x_4014_ = v___x_3993_;
                            v_isShared_4015_ = v_isSharedCheck_4019_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4012_);
                            leanh::lean_dec(v___x_3993_);
                            v___x_4014_ = leanh::lean_box(0);
                            v_isShared_4015_ = v_isSharedCheck_4019_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_selfSets_3981_);
                    leanh::lean_dec(v_contJpId_3980_);
                    leanh::lean_dec_ref(v_args_3979_);
                    leanh::lean_dec_ref(v_info_3978_);
                    leanh::lean_dec_ref(v_decl_3977_);
                    v_a_4020_ = leanh::lean_ctor_get(v___x_3988_, 0);
                    v_isSharedCheck_4027_ = (!leanh::lean_is_exclusive(v___x_3988_)) as u8;
                    if v_isSharedCheck_4027_ == 0 {
                        v___x_4022_ = v___x_3988_;
                        v_isShared_4023_ = v_isSharedCheck_4027_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4020_);
                        leanh::lean_dec(v___x_3988_);
                        v___x_4022_ = leanh::lean_box(0);
                        v_isShared_4023_ = v_isSharedCheck_4027_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4002_ = leanh::lean_unsigned_to_nat(1);
                v___x_4003_ = lean_mk_empty_array_with_capacity(v___x_4002_);
                v___x_4004_ = lean_array_push(v___x_4003_, v___x_3996_);
                v___x_4005_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4005_, 0, v_contJpId_3980_);
                leanh::lean_ctor_set(v___x_4005_, 1, v___x_4004_);
                v___x_4006_ =
                    l_Lean_Compiler_LCNF_attachCodeDecls(v___x_3991_, v_a_3998_, v___x_4005_);
                leanh::lean_dec(v_a_3998_);
                v___x_4007_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4007_, 0, v_a_3994_);
                leanh::lean_ctor_set(v___x_4007_, 1, v___x_4006_);
                if v_isShared_4001_ == 0 {
                    leanh::lean_ctor_set(v___x_4000_, 0, v___x_4007_);
                    v___x_4009_ = v___x_4000_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4010_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4010_, 0, v___x_4007_);
                    v___x_4009_ = v_reuseFailAlloc_4010_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4009_;
            }
            3 => {
                if v_isShared_4015_ == 0 {
                    v___x_4017_ = v___x_4014_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4018_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_a_4012_);
                    v___x_4017_ = v_reuseFailAlloc_4018_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4017_;
            }
            5 => {
                if v_isShared_4023_ == 0 {
                    v___x_4025_ = v___x_4022_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4026_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_a_4020_);
                    v___x_4025_ = v_reuseFailAlloc_4026_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4025_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___boxed(
    mut v_decl_4028_: *mut leanh::LeanObject,
    mut v_info_4029_: *mut leanh::LeanObject,
    mut v_args_4030_: *mut leanh::LeanObject,
    mut v_contJpId_4031_: *mut leanh::LeanObject,
    mut v_selfSets_4032_: *mut leanh::LeanObject,
    mut v_a_4033_: *mut leanh::LeanObject,
    mut v_a_4034_: *mut leanh::LeanObject,
    mut v_a_4035_: *mut leanh::LeanObject,
    mut v_a_4036_: *mut leanh::LeanObject,
    mut v_a_4037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4038_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(v_decl_4028_, v_info_4029_, v_args_4030_, v_contJpId_4031_, v_selfSets_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_);
    leanh::lean_dec(v_a_4036_);
    leanh::lean_dec_ref(v_a_4035_);
    leanh::lean_dec(v_a_4034_);
    leanh::lean_dec_ref(v_a_4033_);
    return v_res_4038_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(
    mut v_alt_4039_: *mut leanh::LeanObject,
    mut v_f_4040_: *mut leanh::LeanObject,
    mut v___y_4041_: *mut leanh::LeanObject,
    mut v___y_4042_: *mut leanh::LeanObject,
    mut v___y_4043_: *mut leanh::LeanObject,
    mut v___y_4044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4052_: u8 = 0;
    let mut v___x_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4057_: u8 = 0;
    let mut v_a_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4061_: u8 = 0;
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4065_: u8 = 0;
    let mut v_code_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_alt_4039_) {
                0 => {
                    v_code_4066_ = leanh::lean_ctor_get(v_alt_4039_, 2);
                    leanh::lean_inc_ref(v_code_4066_);
                    v___y_4047_ = v_code_4066_;
                    state = 1;
                    continue;
                }
                1 => {
                    v_code_4067_ = leanh::lean_ctor_get(v_alt_4039_, 1);
                    leanh::lean_inc_ref(v_code_4067_);
                    v___y_4047_ = v_code_4067_;
                    state = 1;
                    continue;
                }
                _ => {
                    v_code_4068_ = leanh::lean_ctor_get(v_alt_4039_, 0);
                    leanh::lean_inc_ref(v_code_4068_);
                    v___y_4047_ = v_code_4068_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                leanh::lean_inc(v___y_4044_);
                leanh::lean_inc_ref(v___y_4043_);
                leanh::lean_inc(v___y_4042_);
                leanh::lean_inc_ref(v___y_4041_);
                v___x_4048_ = leanh::lean_apply_6(
                    v_f_4040_,
                    v___y_4047_,
                    v___y_4041_,
                    v___y_4042_,
                    v___y_4043_,
                    v___y_4044_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_4048_) == 0 {
                    v_a_4049_ = leanh::lean_ctor_get(v___x_4048_, 0);
                    v_isSharedCheck_4057_ = (!leanh::lean_is_exclusive(v___x_4048_)) as u8;
                    if v_isSharedCheck_4057_ == 0 {
                        v___x_4051_ = v___x_4048_;
                        v_isShared_4052_ = v_isSharedCheck_4057_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4049_);
                        leanh::lean_dec(v___x_4048_);
                        v___x_4051_ = leanh::lean_box(0);
                        v_isShared_4052_ = v_isSharedCheck_4057_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_alt_4039_);
                    v_a_4058_ = leanh::lean_ctor_get(v___x_4048_, 0);
                    v_isSharedCheck_4065_ = (!leanh::lean_is_exclusive(v___x_4048_)) as u8;
                    if v_isSharedCheck_4065_ == 0 {
                        v___x_4060_ = v___x_4048_;
                        v_isShared_4061_ = v_isSharedCheck_4065_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4058_);
                        leanh::lean_dec(v___x_4048_);
                        v___x_4060_ = leanh::lean_box(0);
                        v_isShared_4061_ = v_isSharedCheck_4065_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4053_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_4039_, v_a_4049_);
                if v_isShared_4052_ == 0 {
                    leanh::lean_ctor_set(v___x_4051_, 0, v___x_4053_);
                    v___x_4055_ = v___x_4051_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4056_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4056_, 0, v___x_4053_);
                    v___x_4055_ = v_reuseFailAlloc_4056_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4055_;
            }
            4 => {
                if v_isShared_4061_ == 0 {
                    v___x_4063_ = v___x_4060_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4064_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_a_4058_);
                    v___x_4063_ = v_reuseFailAlloc_4064_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4063_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg___boxed(
    mut v_alt_4069_: *mut leanh::LeanObject,
    mut v_f_4070_: *mut leanh::LeanObject,
    mut v___y_4071_: *mut leanh::LeanObject,
    mut v___y_4072_: *mut leanh::LeanObject,
    mut v___y_4073_: *mut leanh::LeanObject,
    mut v___y_4074_: *mut leanh::LeanObject,
    mut v___y_4075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4076_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_alt_4069_, v_f_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
    leanh::lean_dec(v___y_4074_);
    leanh::lean_dec_ref(v___y_4073_);
    leanh::lean_dec(v___y_4072_);
    leanh::lean_dec_ref(v___y_4071_);
    return v_res_4076_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0(
    mut v_pu_4077_: u8,
    mut v_alt_4078_: *mut leanh::LeanObject,
    mut v_f_4079_: *mut leanh::LeanObject,
    mut v___y_4080_: *mut leanh::LeanObject,
    mut v___y_4081_: *mut leanh::LeanObject,
    mut v___y_4082_: *mut leanh::LeanObject,
    mut v___y_4083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4085_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_alt_4078_, v_f_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_);
    return v___x_4085_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___boxed(
    mut v_pu_4086_: *mut leanh::LeanObject,
    mut v_alt_4087_: *mut leanh::LeanObject,
    mut v_f_4088_: *mut leanh::LeanObject,
    mut v___y_4089_: *mut leanh::LeanObject,
    mut v___y_4090_: *mut leanh::LeanObject,
    mut v___y_4091_: *mut leanh::LeanObject,
    mut v___y_4092_: *mut leanh::LeanObject,
    mut v___y_4093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_4094_: u8 = 0;
    let mut v_res_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4094_ = (leanh::lean_unbox(v_pu_4086_) as u8);
    v_res_4095_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0(v_pu_boxed_4094_, v_alt_4087_, v_f_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
    leanh::lean_dec(v___y_4092_);
    leanh::lean_dec_ref(v___y_4091_);
    leanh::lean_dec(v___y_4090_);
    leanh::lean_dec_ref(v___y_4089_);
    return v_res_4095_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4096_: u8 = 0;
    let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4096_ = 1;
    v___x_4097_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_4096_);
    return v___x_4097_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(
    mut v_msg_4098_: *mut leanh::LeanObject,
    mut v___y_4099_: *mut leanh::LeanObject,
    mut v___y_4100_: *mut leanh::LeanObject,
    mut v___y_4101_: *mut leanh::LeanObject,
    mut v___y_4102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4109_: u8 = 0;
    let mut v_toFunctor_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4116_: u8 = 0;
    let mut v___f_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7095__overap_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4137_: u8 = 0;
    let mut v_unused_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4139_: u8 = 0;
    let mut v_unused_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4104_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0);
                v___x_4105_ = l_StateRefT_x27_instMonad___redArg(v___x_4104_);
                v_toApplicative_4106_ = leanh::lean_ctor_get(v___x_4105_, 0);
                v_isSharedCheck_4139_ = (!leanh::lean_is_exclusive(v___x_4105_)) as u8;
                if v_isSharedCheck_4139_ == 0 {
                    v_unused_4140_ = leanh::lean_ctor_get(v___x_4105_, 1);
                    leanh::lean_dec(v_unused_4140_);
                    v___x_4108_ = v___x_4105_;
                    v_isShared_4109_ = v_isSharedCheck_4139_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_4106_);
                    leanh::lean_dec(v___x_4105_);
                    v___x_4108_ = leanh::lean_box(0);
                    v_isShared_4109_ = v_isSharedCheck_4139_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_4110_ = leanh::lean_ctor_get(v_toApplicative_4106_, 0);
                v_toSeq_4111_ = leanh::lean_ctor_get(v_toApplicative_4106_, 2);
                v_toSeqLeft_4112_ = leanh::lean_ctor_get(v_toApplicative_4106_, 3);
                v_toSeqRight_4113_ = leanh::lean_ctor_get(v_toApplicative_4106_, 4);
                v_isSharedCheck_4137_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_4106_)) as u8;
                if v_isSharedCheck_4137_ == 0 {
                    v_unused_4138_ = leanh::lean_ctor_get(v_toApplicative_4106_, 1);
                    leanh::lean_dec(v_unused_4138_);
                    v___x_4115_ = v_toApplicative_4106_;
                    v_isShared_4116_ = v_isSharedCheck_4137_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_4113_);
                    leanh::lean_inc(v_toSeqLeft_4112_);
                    leanh::lean_inc(v_toSeq_4111_);
                    leanh::lean_inc(v_toFunctor_4110_);
                    leanh::lean_dec(v_toApplicative_4106_);
                    v___x_4115_ = leanh::lean_box(0);
                    v_isShared_4116_ = v_isSharedCheck_4137_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_4117_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1;
                v___f_4118_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2;
                leanh::lean_inc_ref(v_toFunctor_4110_);
                v___f_4119_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4119_, 0, v_toFunctor_4110_);
                v___f_4120_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4120_, 0, v_toFunctor_4110_);
                v___x_4121_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4121_, 0, v___f_4119_);
                leanh::lean_ctor_set(v___x_4121_, 1, v___f_4120_);
                v___f_4122_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4122_, 0, v_toSeqRight_4113_);
                v___f_4123_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4123_, 0, v_toSeqLeft_4112_);
                v___f_4124_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4124_, 0, v_toSeq_4111_);
                if v_isShared_4116_ == 0 {
                    leanh::lean_ctor_set(v___x_4115_, 4, v___f_4122_);
                    leanh::lean_ctor_set(v___x_4115_, 3, v___f_4123_);
                    leanh::lean_ctor_set(v___x_4115_, 2, v___f_4124_);
                    leanh::lean_ctor_set(v___x_4115_, 1, v___f_4117_);
                    leanh::lean_ctor_set(v___x_4115_, 0, v___x_4121_);
                    v___x_4126_ = v___x_4115_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4136_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 0, v___x_4121_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 1, v___f_4117_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 2, v___f_4124_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 3, v___f_4123_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 4, v___f_4122_);
                    v___x_4126_ = v_reuseFailAlloc_4136_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4109_ == 0 {
                    leanh::lean_ctor_set(v___x_4108_, 1, v___f_4118_);
                    leanh::lean_ctor_set(v___x_4108_, 0, v___x_4126_);
                    v___x_4128_ = v___x_4108_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4135_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4135_, 0, v___x_4126_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4135_, 1, v___f_4118_);
                    v___x_4128_ = v_reuseFailAlloc_4135_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4129_ = l_StateRefT_x27_instMonad___redArg(v___x_4128_);
                v___x_4130_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0);
                v___x_4131_ = l_instInhabitedOfMonad___redArg(v___x_4129_, v___x_4130_);
                v___f_4132_ = leanh::lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_4132_, 0, v___x_4131_);
                v___x_7095__overap_4133_ = lean_panic_fn_borrowed(v___f_4132_, v_msg_4098_);
                leanh::lean_dec_ref(v___f_4132_);
                leanh::lean_inc(v___y_4102_);
                leanh::lean_inc_ref(v___y_4101_);
                leanh::lean_inc(v___y_4100_);
                leanh::lean_inc_ref(v___y_4099_);
                v___x_4134_ = leanh::lean_apply_5(
                    v___x_7095__overap_4133_,
                    v___y_4099_,
                    v___y_4100_,
                    v___y_4101_,
                    v___y_4102_,
                    leanh::lean_box(0),
                );
                return v___x_4134_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___boxed(
    mut v_msg_4141_: *mut leanh::LeanObject,
    mut v___y_4142_: *mut leanh::LeanObject,
    mut v___y_4143_: *mut leanh::LeanObject,
    mut v___y_4144_: *mut leanh::LeanObject,
    mut v___y_4145_: *mut leanh::LeanObject,
    mut v___y_4146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4147_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(v_msg_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_);
    leanh::lean_dec(v___y_4145_);
    leanh::lean_dec_ref(v___y_4144_);
    leanh::lean_dec(v___y_4143_);
    leanh::lean_dec_ref(v___y_4142_);
    return v_res_4147_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4154_ = leanh::lean_box(0);
    v___x_4155_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__3;
    v___x_4156_ = l_Lean_Expr_const___override(v___x_4155_, v___x_4154_);
    return v___x_4156_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0___boxed(
    mut v_resetTokenId_4157_: *mut leanh::LeanObject,
    mut v_origAllocId_4158_: *mut leanh::LeanObject,
    mut v_isSharedId_4159_: *mut leanh::LeanObject,
    mut v_resultType_4160_: *mut leanh::LeanObject,
    mut v_x_4161_: *mut leanh::LeanObject,
    mut v___y_4162_: *mut leanh::LeanObject,
    mut v___y_4163_: *mut leanh::LeanObject,
    mut v___y_4164_: *mut leanh::LeanObject,
    mut v___y_4165_: *mut leanh::LeanObject,
    mut v___y_4166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4167_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0(v_resetTokenId_4157_, v_origAllocId_4158_, v_isSharedId_4159_, v_resultType_4160_, v_x_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_);
    leanh::lean_dec(v___y_4165_);
    leanh::lean_dec_ref(v___y_4164_);
    leanh::lean_dec(v___y_4163_);
    leanh::lean_dec_ref(v___y_4162_);
    return v_res_4167_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(
    mut v_resetTokenId_4168_: *mut leanh::LeanObject,
    mut v_origAllocId_4169_: *mut leanh::LeanObject,
    mut v_isSharedId_4170_: *mut leanh::LeanObject,
    mut v_resultType_4171_: *mut leanh::LeanObject,
    mut v_i_4172_: *mut leanh::LeanObject,
    mut v_as_4173_: *mut leanh::LeanObject,
    mut v___y_4174_: *mut leanh::LeanObject,
    mut v___y_4175_: *mut leanh::LeanObject,
    mut v___y_4176_: *mut leanh::LeanObject,
    mut v___y_4177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: u8 = 0;
    let mut v___x_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: usize = 0;
    let mut v___x_4187_: usize = 0;
    let mut v___x_4188_: u8 = 0;
    let mut v___x_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4199_: u8 = 0;
    let mut v___x_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4203_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4179_ = lean_array_get_size(v_as_4173_);
                v___x_4180_ = lean_nat_dec_lt(v_i_4172_, v___x_4179_);
                if v___x_4180_ == 0 {
                    leanh::lean_dec(v_i_4172_);
                    leanh::lean_dec_ref(v_resultType_4171_);
                    leanh::lean_dec(v_isSharedId_4170_);
                    leanh::lean_dec(v_origAllocId_4169_);
                    leanh::lean_dec(v_resetTokenId_4168_);
                    v___x_4181_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4181_, 0, v_as_4173_);
                    return v___x_4181_;
                } else {
                    leanh::lean_inc_ref(v_resultType_4171_);
                    leanh::lean_inc(v_isSharedId_4170_);
                    leanh::lean_inc(v_origAllocId_4169_);
                    leanh::lean_inc(v_resetTokenId_4168_);
                    v___f_4182_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                    leanh::lean_closure_set(v___f_4182_, 0, v_resetTokenId_4168_);
                    leanh::lean_closure_set(v___f_4182_, 1, v_origAllocId_4169_);
                    leanh::lean_closure_set(v___f_4182_, 2, v_isSharedId_4170_);
                    leanh::lean_closure_set(v___f_4182_, 3, v_resultType_4171_);
                    v_a_4183_ = lean_array_fget_borrowed(v_as_4173_, v_i_4172_);
                    leanh::lean_inc(v_a_4183_);
                    v___x_4184_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_a_4183_, v___f_4182_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
                    if leanh::lean_obj_tag(v___x_4184_) == 0 {
                        v_a_4185_ = leanh::lean_ctor_get(v___x_4184_, 0);
                        leanh::lean_inc(v_a_4185_);
                        leanh::lean_dec_ref_known(v___x_4184_, 1);
                        v___x_4186_ = lean_ptr_addr(v_a_4183_);
                        v___x_4187_ = lean_ptr_addr(v_a_4185_);
                        v___x_4188_ = lean_usize_dec_eq(v___x_4186_, v___x_4187_);
                        if v___x_4188_ == 0 {
                            v___x_4189_ = leanh::lean_unsigned_to_nat(1);
                            v___x_4190_ = lean_nat_add(v_i_4172_, v___x_4189_);
                            v___x_4191_ = lean_array_fset(v_as_4173_, v_i_4172_, v_a_4185_);
                            leanh::lean_dec(v_i_4172_);
                            v_i_4172_ = v___x_4190_;
                            v_as_4173_ = v___x_4191_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_4185_);
                            v___x_4193_ = leanh::lean_unsigned_to_nat(1);
                            v___x_4194_ = lean_nat_add(v_i_4172_, v___x_4193_);
                            leanh::lean_dec(v_i_4172_);
                            v_i_4172_ = v___x_4194_;
                            state = 0;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_as_4173_);
                        leanh::lean_dec(v_i_4172_);
                        leanh::lean_dec_ref(v_resultType_4171_);
                        leanh::lean_dec(v_isSharedId_4170_);
                        leanh::lean_dec(v_origAllocId_4169_);
                        leanh::lean_dec(v_resetTokenId_4168_);
                        v_a_4196_ = leanh::lean_ctor_get(v___x_4184_, 0);
                        v_isSharedCheck_4203_ =
                            (!leanh::lean_is_exclusive(v___x_4184_)) as u8;
                        if v_isSharedCheck_4203_ == 0 {
                            v___x_4198_ = v___x_4184_;
                            v_isShared_4199_ = v_isSharedCheck_4203_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4196_);
                            leanh::lean_dec(v___x_4184_);
                            v___x_4198_ = leanh::lean_box(0);
                            v_isShared_4199_ = v_isSharedCheck_4203_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4199_ == 0 {
                    v___x_4201_ = v___x_4198_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4202_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_a_4196_);
                    v___x_4201_ = v_reuseFailAlloc_4202_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4201_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4206_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__6;
    v___x_4207_ = leanh::lean_unsigned_to_nat(6);
    v___x_4208_ = leanh::lean_unsigned_to_nat(208);
    v___x_4209_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5;
    v___x_4210_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1;
    v___x_4211_ = l_mkPanicMessageWithDecl(
        v___x_4210_,
        v___x_4209_,
        v___x_4208_,
        v___x_4207_,
        v___x_4206_,
    );
    return v___x_4211_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(
    mut v_resetTokenId_4212_: *mut leanh::LeanObject,
    mut v_code_4213_: *mut leanh::LeanObject,
    mut v_origAllocId_4214_: *mut leanh::LeanObject,
    mut v_isSharedId_4215_: *mut leanh::LeanObject,
    mut v_currentRetType_4216_: *mut leanh::LeanObject,
    mut v_a_4217_: *mut leanh::LeanObject,
    mut v_a_4218_: *mut leanh::LeanObject,
    mut v_a_4219_: *mut leanh::LeanObject,
    mut v_a_4220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_decl_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_updateHeader_4230_: u8 = 0;
    let mut v_args_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4234_: u8 = 0;
    let mut v___x_4235_: u8 = 0;
    let mut v___x_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4240_: u8 = 0;
    let mut v___x_4241_: usize = 0;
    let mut v___x_4242_: usize = 0;
    let mut v___x_4243_: u8 = 0;
    let mut v___x_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4246_: u8 = 0;
    let mut v___x_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4253_: u8 = 0;
    let mut v_unused_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4259_: u8 = 0;
    let mut v___x_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4262_: u8 = 0;
    let mut v___x_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: u8 = 0;
    let mut v___x_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: u8 = 0;
    let mut v___x_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4295_: u8 = 0;
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4302_: u8 = 0;
    let mut v_a_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4306_: u8 = 0;
    let mut v___x_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4310_: u8 = 0;
    let mut v_a_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4314_: u8 = 0;
    let mut v___x_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4318_: u8 = 0;
    let mut v_reuseFailAlloc_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4323_: u8 = 0;
    let mut v___x_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4327_: u8 = 0;
    let mut v_a_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4331_: u8 = 0;
    let mut v___x_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4335_: u8 = 0;
    let mut v_a_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4339_: u8 = 0;
    let mut v___x_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4343_: u8 = 0;
    let mut v_isSharedCheck_4344_: u8 = 0;
    let mut v_unused_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4347_: u8 = 0;
    let mut v_k_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4353_: u8 = 0;
    let mut v___x_4354_: usize = 0;
    let mut v___x_4355_: usize = 0;
    let mut v___x_4356_: u8 = 0;
    let mut v___x_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4359_: u8 = 0;
    let mut v___x_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4366_: u8 = 0;
    let mut v_unused_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4372_: u8 = 0;
    let mut v_decl_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: u8 = 0;
    let mut v___x_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4387_: u8 = 0;
    let mut v___y_4389_: u8 = 0;
    let mut v___x_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4392_: u8 = 0;
    let mut v___x_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4399_: u8 = 0;
    let mut v_unused_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: usize = 0;
    let mut v___x_4406_: usize = 0;
    let mut v___x_4407_: u8 = 0;
    let mut v___x_4408_: usize = 0;
    let mut v___x_4409_: usize = 0;
    let mut v___x_4410_: u8 = 0;
    let mut v_isSharedCheck_4411_: u8 = 0;
    let mut v_a_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4415_: u8 = 0;
    let mut v___x_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4419_: u8 = 0;
    let mut v_cases_4420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4427_: u8 = 0;
    let mut v___x_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4433_: u8 = 0;
    let mut v___x_4434_: usize = 0;
    let mut v___x_4435_: usize = 0;
    let mut v___x_4436_: u8 = 0;
    let mut v___x_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4439_: u8 = 0;
    let mut v___x_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4449_: u8 = 0;
    let mut v_unused_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4454_: u8 = 0;
    let mut v_a_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4458_: u8 = 0;
    let mut v___x_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4462_: u8 = 0;
    let mut v_isSharedCheck_4463_: u8 = 0;
    let mut v_fvarId_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4472_: u8 = 0;
    let mut v___x_4473_: usize = 0;
    let mut v___x_4474_: usize = 0;
    let mut v___x_4475_: u8 = 0;
    let mut v___x_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4478_: u8 = 0;
    let mut v___x_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4485_: u8 = 0;
    let mut v_unused_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4493_: u8 = 0;
    let mut v_fvarId_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4502_: u8 = 0;
    let mut v___x_4503_: usize = 0;
    let mut v___x_4504_: usize = 0;
    let mut v___x_4505_: u8 = 0;
    let mut v___x_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4508_: u8 = 0;
    let mut v___x_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4515_: u8 = 0;
    let mut v_unused_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4523_: u8 = 0;
    let mut v_fvarId_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4534_: u8 = 0;
    let mut v___x_4535_: usize = 0;
    let mut v___x_4536_: usize = 0;
    let mut v___x_4537_: u8 = 0;
    let mut v___x_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4540_: u8 = 0;
    let mut v___x_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4547_: u8 = 0;
    let mut v_unused_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4557_: u8 = 0;
    let mut v_fvarId_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4565_: u8 = 0;
    let mut v___x_4566_: usize = 0;
    let mut v___x_4567_: usize = 0;
    let mut v___x_4568_: u8 = 0;
    let mut v___x_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4571_: u8 = 0;
    let mut v___x_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4578_: u8 = 0;
    let mut v_unused_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4585_: u8 = 0;
    let mut v_fvarId_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_4588_: u8 = 0;
    let mut v_persistent_4589_: u8 = 0;
    let mut v_k_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4595_: u8 = 0;
    let mut v___x_4596_: usize = 0;
    let mut v___x_4597_: usize = 0;
    let mut v___x_4598_: u8 = 0;
    let mut v___x_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4601_: u8 = 0;
    let mut v___x_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4608_: u8 = 0;
    let mut v_unused_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4615_: u8 = 0;
    let mut v_fvarId_4616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_4618_: u8 = 0;
    let mut v_persistent_4619_: u8 = 0;
    let mut v_objs_x3f_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: u8 = 0;
    let mut v___x_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4627_: u8 = 0;
    let mut v___x_4628_: usize = 0;
    let mut v___x_4629_: usize = 0;
    let mut v___x_4630_: u8 = 0;
    let mut v___x_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4633_: u8 = 0;
    let mut v___x_4635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4640_: u8 = 0;
    let mut v_unused_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4648_: u8 = 0;
    let mut v___x_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: u8 = 0;
    let mut v___x_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4661_: u8 = 0;
    let mut v___x_4662_: usize = 0;
    let mut v___x_4663_: usize = 0;
    let mut v___x_4664_: u8 = 0;
    let mut v___x_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4667_: u8 = 0;
    let mut v___x_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4674_: u8 = 0;
    let mut v_unused_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4680_: u8 = 0;
    let mut v___x_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_code_4213_) {
                0 => {
                    v_decl_4222_ = leanh::lean_ctor_get(v_code_4213_, 0);
                    v_value_4223_ = leanh::lean_ctor_get(v_decl_4222_, 3);
                    leanh::lean_inc(v_value_4223_);
                    if leanh::lean_obj_tag(v_value_4223_) == 12 {
                        v_k_4224_ = leanh::lean_ctor_get(v_code_4213_, 1);
                        v_fvarId_4225_ = leanh::lean_ctor_get(v_decl_4222_, 0);
                        v_binderName_4226_ = leanh::lean_ctor_get(v_decl_4222_, 1);
                        v_type_4227_ = leanh::lean_ctor_get(v_decl_4222_, 2);
                        v_var_4228_ = leanh::lean_ctor_get(v_value_4223_, 0);
                        v_i_4229_ = leanh::lean_ctor_get(v_value_4223_, 1);
                        v_updateHeader_4230_ = leanh::lean_ctor_get_uint8(
                            v_value_4223_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        );
                        v_args_4231_ = leanh::lean_ctor_get(v_value_4223_, 2);
                        v_isSharedCheck_4347_ =
                            (!leanh::lean_is_exclusive(v_value_4223_)) as u8;
                        if v_isSharedCheck_4347_ == 0 {
                            v___x_4233_ = v_value_4223_;
                            v_isShared_4234_ = v_isSharedCheck_4347_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_args_4231_);
                            leanh::lean_inc(v_i_4229_);
                            leanh::lean_inc(v_var_4228_);
                            leanh::lean_dec(v_value_4223_);
                            v___x_4233_ = leanh::lean_box(0);
                            v_isShared_4234_ = v_isSharedCheck_4347_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_value_4223_);
                        v_k_4348_ = leanh::lean_ctor_get(v_code_4213_, 1);
                        leanh::lean_inc_ref(v_k_4348_);
                        v___x_4349_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_4212_, v_k_4348_, v_origAllocId_4214_, v_isSharedId_4215_, v_currentRetType_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                        if leanh::lean_obj_tag(v___x_4349_) == 0 {
                            v_a_4350_ = leanh::lean_ctor_get(v___x_4349_, 0);
                            v_isSharedCheck_4372_ =
                                (!leanh::lean_is_exclusive(v___x_4349_)) as u8;
                            if v_isSharedCheck_4372_ == 0 {
                                v___x_4352_ = v___x_4349_;
                                v_isShared_4353_ = v_isSharedCheck_4372_;
                                state = 22;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4350_);
                                leanh::lean_dec(v___x_4349_);
                                v___x_4352_ = leanh::lean_box(0);
                                v_isShared_4353_ = v_isSharedCheck_4372_;
                                state = 22;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_code_4213_, 2);
                            return v___x_4349_;
                        }
                    }
                }
                2 => {
                    v_decl_4373_ = leanh::lean_ctor_get(v_code_4213_, 0);
                    v_k_4374_ = leanh::lean_ctor_get(v_code_4213_, 1);
                    v_params_4375_ = leanh::lean_ctor_get(v_decl_4373_, 2);
                    v_type_4376_ = leanh::lean_ctor_get(v_decl_4373_, 3);
                    v_value_4377_ = leanh::lean_ctor_get(v_decl_4373_, 4);
                    leanh::lean_inc_ref(v_type_4376_);
                    leanh::lean_inc(v_isSharedId_4215_);
                    leanh::lean_inc(v_origAllocId_4214_);
                    leanh::lean_inc_ref(v_value_4377_);
                    leanh::lean_inc(v_resetTokenId_4212_);
                    v___x_4378_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_4212_, v_value_4377_, v_origAllocId_4214_, v_isSharedId_4215_, v_type_4376_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    if leanh::lean_obj_tag(v___x_4378_) == 0 {
                        v_a_4379_ = leanh::lean_ctor_get(v___x_4378_, 0);
                        leanh::lean_inc(v_a_4379_);
                        leanh::lean_dec_ref_known(v___x_4378_, 1);
                        v___x_4380_ = 1;
                        leanh::lean_inc_ref(v_params_4375_);
                        leanh::lean_inc_ref(v_type_4376_);
                        leanh::lean_inc_ref(v_decl_4373_);
                        v___x_4381_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_4380_, v_decl_4373_, v_type_4376_, v_params_4375_, v_a_4379_, v_a_4218_);
                        if leanh::lean_obj_tag(v___x_4381_) == 0 {
                            v_a_4382_ = leanh::lean_ctor_get(v___x_4381_, 0);
                            leanh::lean_inc(v_a_4382_);
                            leanh::lean_dec_ref_known(v___x_4381_, 1);
                            leanh::lean_inc_ref(v_k_4374_);
                            v___x_4383_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_4212_, v_k_4374_, v_origAllocId_4214_, v_isSharedId_4215_, v_currentRetType_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                            if leanh::lean_obj_tag(v___x_4383_) == 0 {
                                v_a_4384_ = leanh::lean_ctor_get(v___x_4383_, 0);
                                v_isSharedCheck_4411_ =
                                    (!leanh::lean_is_exclusive(v___x_4383_)) as u8;
                                if v_isSharedCheck_4411_ == 0 {
                                    v___x_4386_ = v___x_4383_;
                                    v_isShared_4387_ = v_isSharedCheck_4411_;
                                    state = 27;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4384_);
                                    leanh::lean_dec(v___x_4383_);
                                    v___x_4386_ = leanh::lean_box(0);
                                    v_isShared_4387_ = v_isSharedCheck_4411_;
                                    state = 27;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_4382_);
                                leanh::lean_dec_ref_known(v_code_4213_, 2);
                                return v___x_4383_;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_code_4213_, 2);
                            leanh::lean_dec_ref(v_currentRetType_4216_);
                            leanh::lean_dec(v_isSharedId_4215_);
                            leanh::lean_dec(v_origAllocId_4214_);
                            leanh::lean_dec(v_resetTokenId_4212_);
                            v_a_4412_ = leanh::lean_ctor_get(v___x_4381_, 0);
                            v_isSharedCheck_4419_ =
                                (!leanh::lean_is_exclusive(v___x_4381_)) as u8;
                            if v_isSharedCheck_4419_ == 0 {
                                v___x_4414_ = v___x_4381_;
                                v_isShared_4415_ = v_isSharedCheck_4419_;
                                state = 33;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4412_);
                                leanh::lean_dec(v___x_4381_);
                                v___x_4414_ = leanh::lean_box(0);
                                v_isShared_4415_ = v_isSharedCheck_4419_;
                                state = 33;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_code_4213_, 2);
                        leanh::lean_dec_ref(v_currentRetType_4216_);
                        leanh::lean_dec(v_isSharedId_4215_);
                        leanh::lean_dec(v_origAllocId_4214_);
                        leanh::lean_dec(v_resetTokenId_4212_);
                        return v___x_4378_;
                    }
                }
                4 => {
                    leanh::lean_dec_ref(v_currentRetType_4216_);
                    v_cases_4420_ = leanh::lean_ctor_get(v_code_4213_, 0);
                    leanh::lean_inc_ref(v_cases_4420_);
                    v_typeName_4421_ = leanh::lean_ctor_get(v_cases_4420_, 0);
                    v_resultType_4422_ = leanh::lean_ctor_get(v_cases_4420_, 1);
                    v_discr_4423_ = leanh::lean_ctor_get(v_cases_4420_, 2);
                    v_alts_4424_ = leanh::lean_ctor_get(v_cases_4420_, 3);
                    v_isSharedCheck_4463_ = (!leanh::lean_is_exclusive(v_cases_4420_)) as u8;
                    if v_isSharedCheck_4463_ == 0 {
                        v___x_4426_ = v_cases_4420_;
                        v_isShared_4427_ = v_isSharedCheck_4463_;
                        state = 35;
                        continue;
                    } else {
                        leanh::lean_inc(v_alts_4424_);
                        leanh::lean_inc(v_discr_4423_);
                        leanh::lean_inc(v_resultType_4422_);
                        leanh::lean_inc(v_typeName_4421_);
                        leanh::lean_dec(v_cases_4420_);
                        v___x_4426_ = leanh::lean_box(0);
                        v_isShared_4427_ = v_isSharedCheck_4463_;
                        state = 35;
                        continue;
                    }
                }
                7 => {
                    v_fvarId_4464_ = leanh::lean_ctor_get(v_code_4213_, 0);
                    v_i_4465_ = leanh::lean_ctor_get(v_code_4213_, 1);
                    v_y_4466_ = leanh::lean_ctor_get(v_code_4213_, 2);
                    v_k_4467_ = leanh::lean_ctor_get(v_code_4213_, 3);
                    leanh::lean_inc_ref(v_k_4467_);
                    v___x_4468_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_4212_, v_k_4467_, v_origAllocId_4214_, v_isSharedId_4215_, v_currentRetType_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    if leanh::lean_obj_tag(v___x_4468_) == 0 {
                        v_a_4469_ = leanh::lean_ctor_get(v___x_4468_, 0);
                        v_isSharedCheck_4493_ =
                            (!leanh::lean_is_exclusive(v___x_4468_)) as u8;
                        if v_isSharedCheck_4493_ == 0 {
                            v___x_4471_ = v___x_4468_;
                            v_isShared_4472_ = v_isSharedCheck_4493_;
                            state = 44;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4469_);
                            leanh::lean_dec(v___x_4468_);
                            v___x_4471_ = leanh::lean_box(0);
                            v_isShared_4472_ = v_isSharedCheck_4493_;
                            state = 44;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_code_4213_, 4);
                        return v___x_4468_;
                    }
                }
                8 => {
                    v_fvarId_4494_ = leanh::lean_ctor_get(v_code_4213_, 0);
                    v_i_4495_ = leanh::lean_ctor_get(v_code_4213_, 1);
                    v_y_4496_ = leanh::lean_ctor_get(v_code_4213_, 2);
                    v_k_4497_ = leanh::lean_ctor_get(v_code_4213_, 3);
                    leanh::lean_inc_ref(v_k_4497_);
                    v___x_4498_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_4212_, v_k_4497_, v_origAllocId_4214_, v_isSharedId_4215_, v_currentRetType_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    if leanh::lean_obj_tag(v___x_4498_) == 0 {
                        v_a_4499_ = leanh::lean_ctor_get(v___x_4498_, 0);
                        v_isSharedCheck_4523_ =
                            (!leanh::lean_is_exclusive(v___x_4498_)) as u8;
                        if v_isSharedCheck_4523_ == 0 {
                            v___x_4501_ = v___x_4498_;
                            v_isShared_4502_ = v_isSharedCheck_4523_;
                            state = 49;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4499_);
                            leanh::lean_dec(v___x_4498_);
                            v___x_4501_ = leanh::lean_box(0);
                            v_isShared_4502_ = v_isSharedCheck_4523_;
                            state = 49;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_code_4213_, 4);
                        return v___x_4498_;
                    }
                }
                9 => {
                    v_fvarId_4524_ = leanh::lean_ctor_get(v_code_4213_, 0);
                    v_i_4525_ = leanh::lean_ctor_get(v_code_4213_, 1);
                    v_offset_4526_ = leanh::lean_ctor_get(v_code_4213_, 2);
                    v_y_4527_ = leanh::lean_ctor_get(v_code_4213_, 3);
                    v_ty_4528_ = leanh::lean_ctor_get(v_code_4213_, 4);
                    v_k_4529_ = leanh::lean_ctor_get(v_code_4213_, 5);
                    leanh::lean_inc_ref(v_k_4529_);
                    v___x_4530_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_4212_, v_k_4529_, v_origAllocId_4214_, v_isSharedId_4215_, v_currentRetType_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    if leanh::lean_obj_tag(v___x_4530_) == 0 {
                        v_a_4531_ = leanh::lean_ctor_get(v___x_4530_, 0);
                        v_isSharedCheck_4557_ =
                            (!leanh::lean_is_exclusive(v___x_4530_)) as u8;
                        if v_isSharedCheck_4557_ == 0 {
                            v___x_4533_ = v___x_4530_;
                            v_isShared_4534_ = v_isSharedCheck_4557_;
                            state = 54;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4531_);
                            leanh::lean_dec(v___x_4530_);
                            v___x_4533_ = leanh::lean_box(0);
                            v_isShared_4534_ = v_isSharedCheck_4557_;
                            state = 54;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_code_4213_, 6);
                        return v___x_4530_;
                    }
                }
                10 => {
                    v_fvarId_4558_ = leanh::lean_ctor_get(v_code_4213_, 0);
                    v_cidx_4559_ = leanh::lean_ctor_get(v_code_4213_, 1);
                    v_k_4560_ = leanh::lean_ctor_get(v_code_4213_, 2);
                    leanh::lean_inc_ref(v_k_4560_);
                    v___x_4561_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_4212_, v_k_4560_, v_origAllocId_4214_, v_isSharedId_4215_, v_currentRetType_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    if leanh::lean_obj_tag(v___x_4561_) == 0 {
                        v_a_4562_ = leanh::lean_ctor_get(v___x_4561_, 0);
                        v_isSharedCheck_4585_ =
                            (!leanh::lean_is_exclusive(v___x_4561_)) as u8;
                        if v_isSharedCheck_4585_ == 0 {
                            v___x_4564_ = v___x_4561_;
                            v_isShared_4565_ = v_isSharedCheck_4585_;
                            state = 59;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4562_);
                            leanh::lean_dec(v___x_4561_);
                            v___x_4564_ = leanh::lean_box(0);
                            v_isShared_4565_ = v_isSharedCheck_4585_;
                            state = 59;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_code_4213_, 3);
                        return v___x_4561_;
                    }
                }
                11 => {
                    v_fvarId_4586_ = leanh::lean_ctor_get(v_code_4213_, 0);
                    v_n_4587_ = leanh::lean_ctor_get(v_code_4213_, 1);
                    v_check_4588_ = leanh::lean_ctor_get_uint8(
                        v_code_4213_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    v_persistent_4589_ = leanh::lean_ctor_get_uint8(
                        v_code_4213_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                    );
                    v_k_4590_ = leanh::lean_ctor_get(v_code_4213_, 2);
                    leanh::lean_inc_ref(v_k_4590_);
                    v___x_4591_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_4212_, v_k_4590_, v_origAllocId_4214_, v_isSharedId_4215_, v_currentRetType_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    if leanh::lean_obj_tag(v___x_4591_) == 0 {
                        v_a_4592_ = leanh::lean_ctor_get(v___x_4591_, 0);
                        v_isSharedCheck_4615_ =
                            (!leanh::lean_is_exclusive(v___x_4591_)) as u8;
                        if v_isSharedCheck_4615_ == 0 {
                            v___x_4594_ = v___x_4591_;
                            v_isShared_4595_ = v_isSharedCheck_4615_;
                            state = 64;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4592_);
                            leanh::lean_dec(v___x_4591_);
                            v___x_4594_ = leanh::lean_box(0);
                            v_isShared_4595_ = v_isSharedCheck_4615_;
                            state = 64;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_code_4213_, 3);
                        return v___x_4591_;
                    }
                }
                12 => {
                    v_fvarId_4616_ = leanh::lean_ctor_get(v_code_4213_, 0);
                    v_n_4617_ = leanh::lean_ctor_get(v_code_4213_, 1);
                    v_check_4618_ = leanh::lean_ctor_get_uint8(
                        v_code_4213_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    );
                    v_persistent_4619_ = leanh::lean_ctor_get_uint8(
                        v_code_4213_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
                    );
                    v_objs_x3f_4620_ = leanh::lean_ctor_get(v_code_4213_, 2);
                    v_k_4621_ = leanh::lean_ctor_get(v_code_4213_, 3);
                    v___x_4622_ = l_Lean_instBEqFVarId_beq(v_resetTokenId_4212_, v_fvarId_4616_);
                    if v___x_4622_ == 0 {
                        leanh::lean_inc_ref(v_k_4621_);
                        v___x_4623_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_4212_, v_k_4621_, v_origAllocId_4214_, v_isSharedId_4215_, v_currentRetType_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                        if leanh::lean_obj_tag(v___x_4623_) == 0 {
                            v_a_4624_ = leanh::lean_ctor_get(v___x_4623_, 0);
                            v_isSharedCheck_4648_ =
                                (!leanh::lean_is_exclusive(v___x_4623_)) as u8;
                            if v_isSharedCheck_4648_ == 0 {
                                v___x_4626_ = v___x_4623_;
                                v_isShared_4627_ = v_isSharedCheck_4648_;
                                state = 69;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4624_);
                                leanh::lean_dec(v___x_4623_);
                                v___x_4626_ = leanh::lean_box(0);
                                v_isShared_4627_ = v_isSharedCheck_4648_;
                                state = 69;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_code_4213_, 4);
                            return v___x_4623_;
                        }
                    } else {
                        leanh::lean_inc_ref(v_k_4621_);
                        leanh::lean_inc(v_n_4617_);
                        leanh::lean_dec_ref_known(v_code_4213_, 4);
                        leanh::lean_dec_ref(v_currentRetType_4216_);
                        leanh::lean_dec(v_isSharedId_4215_);
                        leanh::lean_dec(v_origAllocId_4214_);
                        v___x_4649_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4650_ = lean_nat_dec_eq(v_n_4617_, v___x_4649_);
                        leanh::lean_dec(v_n_4617_);
                        if v___x_4650_ == 0 {
                            leanh::lean_dec_ref(v_k_4621_);
                            leanh::lean_dec(v_resetTokenId_4212_);
                            v___x_4651_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7_once), _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7);
                            v___x_4652_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(v___x_4651_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                            return v___x_4652_;
                        } else {
                            v___x_4653_ = leanh::lean_alloc_ctor(13, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4653_, 0, v_resetTokenId_4212_);
                            leanh::lean_ctor_set(v___x_4653_, 1, v_k_4621_);
                            v___x_4654_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_4654_, 0, v___x_4653_);
                            return v___x_4654_;
                        }
                    }
                }
                13 => {
                    v_fvarId_4655_ = leanh::lean_ctor_get(v_code_4213_, 0);
                    v_k_4656_ = leanh::lean_ctor_get(v_code_4213_, 1);
                    leanh::lean_inc_ref(v_k_4656_);
                    v___x_4657_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_4212_, v_k_4656_, v_origAllocId_4214_, v_isSharedId_4215_, v_currentRetType_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    if leanh::lean_obj_tag(v___x_4657_) == 0 {
                        v_a_4658_ = leanh::lean_ctor_get(v___x_4657_, 0);
                        v_isSharedCheck_4680_ =
                            (!leanh::lean_is_exclusive(v___x_4657_)) as u8;
                        if v_isSharedCheck_4680_ == 0 {
                            v___x_4660_ = v___x_4657_;
                            v_isShared_4661_ = v_isSharedCheck_4680_;
                            state = 74;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4658_);
                            leanh::lean_dec(v___x_4657_);
                            v___x_4660_ = leanh::lean_box(0);
                            v_isShared_4661_ = v_isSharedCheck_4680_;
                            state = 74;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_code_4213_, 2);
                        return v___x_4657_;
                    }
                }
                _ => {
                    leanh::lean_dec_ref(v_currentRetType_4216_);
                    leanh::lean_dec(v_isSharedId_4215_);
                    leanh::lean_dec(v_origAllocId_4214_);
                    leanh::lean_dec(v_resetTokenId_4212_);
                    v___x_4681_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4681_, 0, v_code_4213_);
                    return v___x_4681_;
                }
            },
            1 => {
                v___x_4235_ = l_Lean_instBEqFVarId_beq(v_resetTokenId_4212_, v_var_4228_);
                leanh::lean_dec(v_var_4228_);
                if v___x_4235_ == 0 {
                    leanh::lean_del_object(v___x_4233_);
                    leanh::lean_dec_ref(v_args_4231_);
                    leanh::lean_dec_ref(v_i_4229_);
                    leanh::lean_inc_ref(v_k_4224_);
                    v___x_4236_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_4212_, v_k_4224_, v_origAllocId_4214_, v_isSharedId_4215_, v_currentRetType_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    if leanh::lean_obj_tag(v___x_4236_) == 0 {
                        v_a_4237_ = leanh::lean_ctor_get(v___x_4236_, 0);
                        v_isSharedCheck_4259_ =
                            (!leanh::lean_is_exclusive(v___x_4236_)) as u8;
                        if v_isSharedCheck_4259_ == 0 {
                            v___x_4239_ = v___x_4236_;
                            v_isShared_4240_ = v_isSharedCheck_4259_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4237_);
                            leanh::lean_dec(v___x_4236_);
                            v___x_4239_ = leanh::lean_box(0);
                            v_isShared_4240_ = v_isSharedCheck_4259_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_code_4213_, 2);
                        return v___x_4236_;
                    }
                } else {
                    leanh::lean_inc_ref(v_k_4224_);
                    leanh::lean_inc_ref(v_decl_4222_);
                    v_isSharedCheck_4344_ = (!leanh::lean_is_exclusive(v_code_4213_)) as u8;
                    if v_isSharedCheck_4344_ == 0 {
                        v_unused_4345_ = leanh::lean_ctor_get(v_code_4213_, 1);
                        leanh::lean_dec(v_unused_4345_);
                        v_unused_4346_ = leanh::lean_ctor_get(v_code_4213_, 0);
                        leanh::lean_dec(v_unused_4346_);
                        v___x_4261_ = v_code_4213_;
                        v_isShared_4262_ = v_isSharedCheck_4344_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_dec(v_code_4213_);
                        v___x_4261_ = leanh::lean_box(0);
                        v_isShared_4262_ = v_isSharedCheck_4344_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4241_ = lean_ptr_addr(v_k_4224_);
                v___x_4242_ = lean_ptr_addr(v_a_4237_);
                v___x_4243_ = lean_usize_dec_eq(v___x_4241_, v___x_4242_);
                if v___x_4243_ == 0 {
                    leanh::lean_inc_ref(v_decl_4222_);
                    v_isSharedCheck_4253_ = (!leanh::lean_is_exclusive(v_code_4213_)) as u8;
                    if v_isSharedCheck_4253_ == 0 {
                        v_unused_4254_ = leanh::lean_ctor_get(v_code_4213_, 1);
                        leanh::lean_dec(v_unused_4254_);
                        v_unused_4255_ = leanh::lean_ctor_get(v_code_4213_, 0);
                        leanh::lean_dec(v_unused_4255_);
                        v___x_4245_ = v_code_4213_;
                        v_isShared_4246_ = v_isSharedCheck_4253_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_code_4213_);
                        v___x_4245_ = leanh::lean_box(0);
                        v_isShared_4246_ = v_isSharedCheck_4253_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4237_);
                    if v_isShared_4240_ == 0 {
                        leanh::lean_ctor_set(v___x_4239_, 0, v_code_4213_);
                        v___x_4257_ = v___x_4239_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4258_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_code_4213_);
                        v___x_4257_ = v_reuseFailAlloc_4258_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4246_ == 0 {
                    leanh::lean_ctor_set(v___x_4245_, 1, v_a_4237_);
                    v___x_4248_ = v___x_4245_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4252_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_decl_4222_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4252_, 1, v_a_4237_);
                    v___x_4248_ = v_reuseFailAlloc_4252_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4240_ == 0 {
                    leanh::lean_ctor_set(v___x_4239_, 0, v___x_4248_);
                    v___x_4250_ = v___x_4239_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4251_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4251_, 0, v___x_4248_);
                    v___x_4250_ = v_reuseFailAlloc_4251_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4250_;
            }
            6 => {
                return v___x_4257_;
            }
            7 => {
                v___x_4263_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(v_fvarId_4225_, v_k_4224_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                if leanh::lean_obj_tag(v___x_4263_) == 0 {
                    v_a_4264_ = leanh::lean_ctor_get(v___x_4263_, 0);
                    leanh::lean_inc(v_a_4264_);
                    leanh::lean_dec_ref_known(v___x_4263_, 1);
                    v_fst_4265_ = leanh::lean_ctor_get(v_a_4264_, 0);
                    leanh::lean_inc(v_fst_4265_);
                    v_snd_4266_ = leanh::lean_ctor_get(v_a_4264_, 1);
                    leanh::lean_inc(v_snd_4266_);
                    leanh::lean_dec(v_a_4264_);
                    v___x_4267_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(v_origAllocId_4214_, v_fst_4265_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    leanh::lean_dec(v_fst_4265_);
                    if leanh::lean_obj_tag(v___x_4267_) == 0 {
                        v_a_4268_ = leanh::lean_ctor_get(v___x_4267_, 0);
                        leanh::lean_inc(v_a_4268_);
                        leanh::lean_dec_ref_known(v___x_4267_, 1);
                        v_fst_4269_ = leanh::lean_ctor_get(v_a_4268_, 0);
                        leanh::lean_inc(v_fst_4269_);
                        v_snd_4270_ = leanh::lean_ctor_get(v_a_4268_, 1);
                        leanh::lean_inc(v_snd_4270_);
                        leanh::lean_dec(v_a_4268_);
                        v___x_4271_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__1;
                        v___x_4272_ =
                            l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4271_, v_a_4218_);
                        if leanh::lean_obj_tag(v___x_4272_) == 0 {
                            v_a_4273_ = leanh::lean_ctor_get(v___x_4272_, 0);
                            leanh::lean_inc(v_a_4273_);
                            leanh::lean_dec_ref_known(v___x_4272_, 1);
                            v___x_4274_ = 1;
                            v___x_4275_ = l_Lean_Compiler_LCNF_attachCodeDecls(
                                v___x_4274_,
                                v_snd_4270_,
                                v_snd_4266_,
                            );
                            leanh::lean_dec(v_snd_4270_);
                            v___x_4276_ = 0;
                            leanh::lean_inc_ref(v_type_4227_);
                            leanh::lean_inc(v_binderName_4226_);
                            leanh::lean_inc(v_fvarId_4225_);
                            if v_isShared_4234_ == 0 {
                                leanh::lean_ctor_set_tag(v___x_4233_, 0);
                                leanh::lean_ctor_set(v___x_4233_, 2, v_type_4227_);
                                leanh::lean_ctor_set(v___x_4233_, 1, v_binderName_4226_);
                                leanh::lean_ctor_set(v___x_4233_, 0, v_fvarId_4225_);
                                v___x_4278_ = v___x_4233_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_4319_ =
                                    leanh::lean_alloc_ctor(0, 3, (1) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4319_,
                                    0,
                                    v_fvarId_4225_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4319_,
                                    1,
                                    v_binderName_4226_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4319_,
                                    2,
                                    v_type_4227_,
                                );
                                v___x_4278_ = v_reuseFailAlloc_4319_;
                                state = 8;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_snd_4270_);
                            leanh::lean_dec(v_fst_4269_);
                            leanh::lean_dec(v_snd_4266_);
                            leanh::lean_del_object(v___x_4261_);
                            leanh::lean_del_object(v___x_4233_);
                            leanh::lean_dec_ref(v_args_4231_);
                            leanh::lean_dec_ref(v_i_4229_);
                            leanh::lean_dec_ref(v_decl_4222_);
                            leanh::lean_dec_ref(v_currentRetType_4216_);
                            leanh::lean_dec(v_isSharedId_4215_);
                            leanh::lean_dec(v_origAllocId_4214_);
                            leanh::lean_dec(v_resetTokenId_4212_);
                            v_a_4320_ = leanh::lean_ctor_get(v___x_4272_, 0);
                            v_isSharedCheck_4327_ =
                                (!leanh::lean_is_exclusive(v___x_4272_)) as u8;
                            if v_isSharedCheck_4327_ == 0 {
                                v___x_4322_ = v___x_4272_;
                                v_isShared_4323_ = v_isSharedCheck_4327_;
                                state = 16;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4320_);
                                leanh::lean_dec(v___x_4272_);
                                v___x_4322_ = leanh::lean_box(0);
                                v_isShared_4323_ = v_isSharedCheck_4327_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_snd_4266_);
                        leanh::lean_del_object(v___x_4261_);
                        leanh::lean_del_object(v___x_4233_);
                        leanh::lean_dec_ref(v_args_4231_);
                        leanh::lean_dec_ref(v_i_4229_);
                        leanh::lean_dec_ref(v_decl_4222_);
                        leanh::lean_dec_ref(v_currentRetType_4216_);
                        leanh::lean_dec(v_isSharedId_4215_);
                        leanh::lean_dec(v_origAllocId_4214_);
                        leanh::lean_dec(v_resetTokenId_4212_);
                        v_a_4328_ = leanh::lean_ctor_get(v___x_4267_, 0);
                        v_isSharedCheck_4335_ =
                            (!leanh::lean_is_exclusive(v___x_4267_)) as u8;
                        if v_isSharedCheck_4335_ == 0 {
                            v___x_4330_ = v___x_4267_;
                            v_isShared_4331_ = v_isSharedCheck_4335_;
                            state = 18;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4328_);
                            leanh::lean_dec(v___x_4267_);
                            v___x_4330_ = leanh::lean_box(0);
                            v_isShared_4331_ = v_isSharedCheck_4335_;
                            state = 18;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_4261_);
                    leanh::lean_del_object(v___x_4233_);
                    leanh::lean_dec_ref(v_args_4231_);
                    leanh::lean_dec_ref(v_i_4229_);
                    leanh::lean_dec_ref(v_decl_4222_);
                    leanh::lean_dec_ref(v_currentRetType_4216_);
                    leanh::lean_dec(v_isSharedId_4215_);
                    leanh::lean_dec(v_origAllocId_4214_);
                    leanh::lean_dec(v_resetTokenId_4212_);
                    v_a_4336_ = leanh::lean_ctor_get(v___x_4263_, 0);
                    v_isSharedCheck_4343_ = (!leanh::lean_is_exclusive(v___x_4263_)) as u8;
                    if v_isSharedCheck_4343_ == 0 {
                        v___x_4338_ = v___x_4263_;
                        v_isShared_4339_ = v_isSharedCheck_4343_;
                        state = 20;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4336_);
                        leanh::lean_dec(v___x_4263_);
                        v___x_4338_ = leanh::lean_box(0);
                        v_isShared_4339_ = v_isSharedCheck_4343_;
                        state = 20;
                        continue;
                    }
                }
            }
            8 => {
                leanh::lean_ctor_set_uint8(
                    v___x_4278_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_4276_,
                );
                v___x_4279_ = leanh::lean_unsigned_to_nat(1);
                v___x_4280_ = lean_mk_empty_array_with_capacity(v___x_4279_);
                v___x_4281_ = lean_array_push(v___x_4280_, v___x_4278_);
                leanh::lean_inc_ref(v_currentRetType_4216_);
                v___x_4282_ = l_Lean_Compiler_LCNF_mkFunDecl(
                    v___x_4274_,
                    v_a_4273_,
                    v_currentRetType_4216_,
                    v___x_4281_,
                    v___x_4275_,
                    v_a_4217_,
                    v_a_4218_,
                    v_a_4219_,
                    v_a_4220_,
                );
                if leanh::lean_obj_tag(v___x_4282_) == 0 {
                    v_a_4283_ = leanh::lean_ctor_get(v___x_4282_, 0);
                    leanh::lean_inc(v_a_4283_);
                    leanh::lean_dec_ref_known(v___x_4282_, 1);
                    v_fvarId_4284_ = leanh::lean_ctor_get(v_a_4283_, 0);
                    leanh::lean_inc(v_fvarId_4284_);
                    leanh::lean_inc_ref(v_args_4231_);
                    leanh::lean_inc_ref(v_i_4229_);
                    leanh::lean_inc_ref(v_decl_4222_);
                    v___x_4285_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(v_decl_4222_, v_i_4229_, v_args_4231_, v_fvarId_4284_, v_fst_4269_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    if leanh::lean_obj_tag(v___x_4285_) == 0 {
                        v_a_4286_ = leanh::lean_ctor_get(v___x_4285_, 0);
                        leanh::lean_inc(v_a_4286_);
                        leanh::lean_dec_ref_known(v___x_4285_, 1);
                        leanh::lean_inc(v_fvarId_4284_);
                        v___x_4287_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(v_resetTokenId_4212_, v_i_4229_, v_updateHeader_4230_, v_args_4231_, v_fvarId_4284_, v_origAllocId_4214_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                        leanh::lean_dec(v_origAllocId_4214_);
                        leanh::lean_dec_ref(v_args_4231_);
                        leanh::lean_dec_ref(v_i_4229_);
                        if leanh::lean_obj_tag(v___x_4287_) == 0 {
                            v_a_4288_ = leanh::lean_ctor_get(v___x_4287_, 0);
                            leanh::lean_inc(v_a_4288_);
                            leanh::lean_dec_ref_known(v___x_4287_, 1);
                            v___x_4289_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(
                                v___x_4274_,
                                v_decl_4222_,
                                v_a_4218_,
                            );
                            leanh::lean_dec_ref(v_decl_4222_);
                            if leanh::lean_obj_tag(v___x_4289_) == 0 {
                                leanh::lean_dec_ref_known(v___x_4289_, 1);
                                v___x_4290_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4_once), _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4);
                                v___x_4291_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_isSharedId_4215_, v___x_4290_, v_currentRetType_4216_, v_a_4286_, v_a_4288_);
                                if leanh::lean_obj_tag(v___x_4291_) == 0 {
                                    v_a_4292_ = leanh::lean_ctor_get(v___x_4291_, 0);
                                    v_isSharedCheck_4302_ =
                                        (!leanh::lean_is_exclusive(v___x_4291_)) as u8;
                                    if v_isSharedCheck_4302_ == 0 {
                                        v___x_4294_ = v___x_4291_;
                                        v_isShared_4295_ = v_isSharedCheck_4302_;
                                        state = 9;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4292_);
                                        leanh::lean_dec(v___x_4291_);
                                        v___x_4294_ = leanh::lean_box(0);
                                        v_isShared_4295_ = v_isSharedCheck_4302_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_4283_);
                                    leanh::lean_del_object(v___x_4261_);
                                    return v___x_4291_;
                                }
                            } else {
                                leanh::lean_dec(v_a_4288_);
                                leanh::lean_dec(v_a_4286_);
                                leanh::lean_dec(v_a_4283_);
                                leanh::lean_del_object(v___x_4261_);
                                leanh::lean_dec_ref(v_currentRetType_4216_);
                                leanh::lean_dec(v_isSharedId_4215_);
                                v_a_4303_ = leanh::lean_ctor_get(v___x_4289_, 0);
                                v_isSharedCheck_4310_ =
                                    (!leanh::lean_is_exclusive(v___x_4289_)) as u8;
                                if v_isSharedCheck_4310_ == 0 {
                                    v___x_4305_ = v___x_4289_;
                                    v_isShared_4306_ = v_isSharedCheck_4310_;
                                    state = 12;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4303_);
                                    leanh::lean_dec(v___x_4289_);
                                    v___x_4305_ = leanh::lean_box(0);
                                    v_isShared_4306_ = v_isSharedCheck_4310_;
                                    state = 12;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_4286_);
                            leanh::lean_dec(v_a_4283_);
                            leanh::lean_del_object(v___x_4261_);
                            leanh::lean_dec_ref(v_decl_4222_);
                            leanh::lean_dec_ref(v_currentRetType_4216_);
                            leanh::lean_dec(v_isSharedId_4215_);
                            return v___x_4287_;
                        }
                    } else {
                        leanh::lean_dec(v_a_4283_);
                        leanh::lean_del_object(v___x_4261_);
                        leanh::lean_dec_ref(v_args_4231_);
                        leanh::lean_dec_ref(v_i_4229_);
                        leanh::lean_dec_ref(v_decl_4222_);
                        leanh::lean_dec_ref(v_currentRetType_4216_);
                        leanh::lean_dec(v_isSharedId_4215_);
                        leanh::lean_dec(v_origAllocId_4214_);
                        leanh::lean_dec(v_resetTokenId_4212_);
                        return v___x_4285_;
                    }
                } else {
                    leanh::lean_dec(v_fst_4269_);
                    leanh::lean_del_object(v___x_4261_);
                    leanh::lean_dec_ref(v_args_4231_);
                    leanh::lean_dec_ref(v_i_4229_);
                    leanh::lean_dec_ref(v_decl_4222_);
                    leanh::lean_dec_ref(v_currentRetType_4216_);
                    leanh::lean_dec(v_isSharedId_4215_);
                    leanh::lean_dec(v_origAllocId_4214_);
                    leanh::lean_dec(v_resetTokenId_4212_);
                    v_a_4311_ = leanh::lean_ctor_get(v___x_4282_, 0);
                    v_isSharedCheck_4318_ = (!leanh::lean_is_exclusive(v___x_4282_)) as u8;
                    if v_isSharedCheck_4318_ == 0 {
                        v___x_4313_ = v___x_4282_;
                        v_isShared_4314_ = v_isSharedCheck_4318_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4311_);
                        leanh::lean_dec(v___x_4282_);
                        v___x_4313_ = leanh::lean_box(0);
                        v_isShared_4314_ = v_isSharedCheck_4318_;
                        state = 14;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_4262_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4261_, 2);
                    leanh::lean_ctor_set(v___x_4261_, 1, v_a_4292_);
                    leanh::lean_ctor_set(v___x_4261_, 0, v_a_4283_);
                    v___x_4297_ = v___x_4261_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4301_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4301_, 0, v_a_4283_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4301_, 1, v_a_4292_);
                    v___x_4297_ = v_reuseFailAlloc_4301_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_4295_ == 0 {
                    leanh::lean_ctor_set(v___x_4294_, 0, v___x_4297_);
                    v___x_4299_ = v___x_4294_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4300_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4300_, 0, v___x_4297_);
                    v___x_4299_ = v_reuseFailAlloc_4300_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4299_;
            }
            12 => {
                if v_isShared_4306_ == 0 {
                    v___x_4308_ = v___x_4305_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4309_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4309_, 0, v_a_4303_);
                    v___x_4308_ = v_reuseFailAlloc_4309_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4308_;
            }
            14 => {
                if v_isShared_4314_ == 0 {
                    v___x_4316_ = v___x_4313_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4317_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4317_, 0, v_a_4311_);
                    v___x_4316_ = v_reuseFailAlloc_4317_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4316_;
            }
            16 => {
                if v_isShared_4323_ == 0 {
                    v___x_4325_ = v___x_4322_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4326_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_a_4320_);
                    v___x_4325_ = v_reuseFailAlloc_4326_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4325_;
            }
            18 => {
                if v_isShared_4331_ == 0 {
                    v___x_4333_ = v___x_4330_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4334_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4334_, 0, v_a_4328_);
                    v___x_4333_ = v_reuseFailAlloc_4334_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4333_;
            }
            20 => {
                if v_isShared_4339_ == 0 {
                    v___x_4341_ = v___x_4338_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4342_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_a_4336_);
                    v___x_4341_ = v_reuseFailAlloc_4342_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_4341_;
            }
            22 => {
                v___x_4354_ = lean_ptr_addr(v_k_4348_);
                v___x_4355_ = lean_ptr_addr(v_a_4350_);
                v___x_4356_ = lean_usize_dec_eq(v___x_4354_, v___x_4355_);
                if v___x_4356_ == 0 {
                    leanh::lean_inc_ref(v_decl_4222_);
                    v_isSharedCheck_4366_ = (!leanh::lean_is_exclusive(v_code_4213_)) as u8;
                    if v_isSharedCheck_4366_ == 0 {
                        v_unused_4367_ = leanh::lean_ctor_get(v_code_4213_, 1);
                        leanh::lean_dec(v_unused_4367_);
                        v_unused_4368_ = leanh::lean_ctor_get(v_code_4213_, 0);
                        leanh::lean_dec(v_unused_4368_);
                        v___x_4358_ = v_code_4213_;
                        v_isShared_4359_ = v_isSharedCheck_4366_;
                        state = 23;
                        continue;
                    } else {
                        leanh::lean_dec(v_code_4213_);
                        v___x_4358_ = leanh::lean_box(0);
                        v_isShared_4359_ = v_isSharedCheck_4366_;
                        state = 23;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4350_);
                    if v_isShared_4353_ == 0 {
                        leanh::lean_ctor_set(v___x_4352_, 0, v_code_4213_);
                        v___x_4370_ = v___x_4352_;
                        state = 26;
                        continue;
                    } else {
                        v_reuseFailAlloc_4371_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4371_, 0, v_code_4213_);
                        v___x_4370_ = v_reuseFailAlloc_4371_;
                        state = 26;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_4359_ == 0 {
                    leanh::lean_ctor_set(v___x_4358_, 1, v_a_4350_);
                    v___x_4361_ = v___x_4358_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4365_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_decl_4222_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4365_, 1, v_a_4350_);
                    v___x_4361_ = v_reuseFailAlloc_4365_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                if v_isShared_4353_ == 0 {
                    leanh::lean_ctor_set(v___x_4352_, 0, v___x_4361_);
                    v___x_4363_ = v___x_4352_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_4364_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4364_, 0, v___x_4361_);
                    v___x_4363_ = v_reuseFailAlloc_4364_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_4363_;
            }
            26 => {
                return v___x_4370_;
            }
            27 => {
                v___x_4405_ = lean_ptr_addr(v_k_4374_);
                v___x_4406_ = lean_ptr_addr(v_a_4384_);
                v___x_4407_ = lean_usize_dec_eq(v___x_4405_, v___x_4406_);
                if v___x_4407_ == 0 {
                    v___y_4389_ = v___x_4407_;
                    state = 28;
                    continue;
                } else {
                    v___x_4408_ = lean_ptr_addr(v_decl_4373_);
                    v___x_4409_ = lean_ptr_addr(v_a_4382_);
                    v___x_4410_ = lean_usize_dec_eq(v___x_4408_, v___x_4409_);
                    v___y_4389_ = v___x_4410_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v___y_4389_ == 0 {
                    v_isSharedCheck_4399_ = (!leanh::lean_is_exclusive(v_code_4213_)) as u8;
                    if v_isSharedCheck_4399_ == 0 {
                        v_unused_4400_ = leanh::lean_ctor_get(v_code_4213_, 1);
                        leanh::lean_dec(v_unused_4400_);
                        v_unused_4401_ = leanh::lean_ctor_get(v_code_4213_, 0);
                        leanh::lean_dec(v_unused_4401_);
                        v___x_4391_ = v_code_4213_;
                        v_isShared_4392_ = v_isSharedCheck_4399_;
                        state = 29;
                        continue;
                    } else {
                        leanh::lean_dec(v_code_4213_);
                        v___x_4391_ = leanh::lean_box(0);
                        v_isShared_4392_ = v_isSharedCheck_4399_;
                        state = 29;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4384_);
                    leanh::lean_dec(v_a_4382_);
                    if v_isShared_4387_ == 0 {
                        leanh::lean_ctor_set(v___x_4386_, 0, v_code_4213_);
                        v___x_4403_ = v___x_4386_;
                        state = 32;
                        continue;
                    } else {
                        v_reuseFailAlloc_4404_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4404_, 0, v_code_4213_);
                        v___x_4403_ = v_reuseFailAlloc_4404_;
                        state = 32;
                        continue;
                    }
                }
            }
            29 => {
                if v_isShared_4392_ == 0 {
                    leanh::lean_ctor_set(v___x_4391_, 1, v_a_4384_);
                    leanh::lean_ctor_set(v___x_4391_, 0, v_a_4382_);
                    v___x_4394_ = v___x_4391_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_4398_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4398_, 0, v_a_4382_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4398_, 1, v_a_4384_);
                    v___x_4394_ = v_reuseFailAlloc_4398_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                if v_isShared_4387_ == 0 {
                    leanh::lean_ctor_set(v___x_4386_, 0, v___x_4394_);
                    v___x_4396_ = v___x_4386_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_4397_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4397_, 0, v___x_4394_);
                    v___x_4396_ = v_reuseFailAlloc_4397_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_4396_;
            }
            32 => {
                return v___x_4403_;
            }
            33 => {
                if v_isShared_4415_ == 0 {
                    v___x_4417_ = v___x_4414_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_4418_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_a_4412_);
                    v___x_4417_ = v_reuseFailAlloc_4418_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_4417_;
            }
            35 => {
                v___x_4428_ = leanh::lean_unsigned_to_nat(0);
                leanh::lean_inc_ref(v_alts_4424_);
                leanh::lean_inc_ref(v_resultType_4422_);
                v___x_4429_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(v_resetTokenId_4212_, v_origAllocId_4214_, v_isSharedId_4215_, v_resultType_4422_, v___x_4428_, v_alts_4424_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                if leanh::lean_obj_tag(v___x_4429_) == 0 {
                    v_a_4430_ = leanh::lean_ctor_get(v___x_4429_, 0);
                    v_isSharedCheck_4454_ = (!leanh::lean_is_exclusive(v___x_4429_)) as u8;
                    if v_isSharedCheck_4454_ == 0 {
                        v___x_4432_ = v___x_4429_;
                        v_isShared_4433_ = v_isSharedCheck_4454_;
                        state = 36;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4430_);
                        leanh::lean_dec(v___x_4429_);
                        v___x_4432_ = leanh::lean_box(0);
                        v_isShared_4433_ = v_isSharedCheck_4454_;
                        state = 36;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4426_);
                    leanh::lean_dec_ref(v_alts_4424_);
                    leanh::lean_dec(v_discr_4423_);
                    leanh::lean_dec_ref(v_resultType_4422_);
                    leanh::lean_dec(v_typeName_4421_);
                    leanh::lean_dec_ref_known(v_code_4213_, 1);
                    v_a_4455_ = leanh::lean_ctor_get(v___x_4429_, 0);
                    v_isSharedCheck_4462_ = (!leanh::lean_is_exclusive(v___x_4429_)) as u8;
                    if v_isSharedCheck_4462_ == 0 {
                        v___x_4457_ = v___x_4429_;
                        v_isShared_4458_ = v_isSharedCheck_4462_;
                        state = 42;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4455_);
                        leanh::lean_dec(v___x_4429_);
                        v___x_4457_ = leanh::lean_box(0);
                        v_isShared_4458_ = v_isSharedCheck_4462_;
                        state = 42;
                        continue;
                    }
                }
            }
            36 => {
                v___x_4434_ = lean_ptr_addr(v_alts_4424_);
                leanh::lean_dec_ref(v_alts_4424_);
                v___x_4435_ = lean_ptr_addr(v_a_4430_);
                v___x_4436_ = lean_usize_dec_eq(v___x_4434_, v___x_4435_);
                if v___x_4436_ == 0 {
                    v_isSharedCheck_4449_ = (!leanh::lean_is_exclusive(v_code_4213_)) as u8;
                    if v_isSharedCheck_4449_ == 0 {
                        v_unused_4450_ = leanh::lean_ctor_get(v_code_4213_, 0);
                        leanh::lean_dec(v_unused_4450_);
                        v___x_4438_ = v_code_4213_;
                        v_isShared_4439_ = v_isSharedCheck_4449_;
                        state = 37;
                        continue;
                    } else {
                        leanh::lean_dec(v_code_4213_);
                        v___x_4438_ = leanh::lean_box(0);
                        v_isShared_4439_ = v_isSharedCheck_4449_;
                        state = 37;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4430_);
                    leanh::lean_del_object(v___x_4426_);
                    leanh::lean_dec(v_discr_4423_);
                    leanh::lean_dec_ref(v_resultType_4422_);
                    leanh::lean_dec(v_typeName_4421_);
                    if v_isShared_4433_ == 0 {
                        leanh::lean_ctor_set(v___x_4432_, 0, v_code_4213_);
                        v___x_4452_ = v___x_4432_;
                        state = 41;
                        continue;
                    } else {
                        v_reuseFailAlloc_4453_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_code_4213_);
                        v___x_4452_ = v_reuseFailAlloc_4453_;
                        state = 41;
                        continue;
                    }
                }
            }
            37 => {
                if v_isShared_4427_ == 0 {
                    leanh::lean_ctor_set(v___x_4426_, 3, v_a_4430_);
                    v___x_4441_ = v___x_4426_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_4448_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4448_, 0, v_typeName_4421_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4448_, 1, v_resultType_4422_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4448_, 2, v_discr_4423_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4448_, 3, v_a_4430_);
                    v___x_4441_ = v_reuseFailAlloc_4448_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                if v_isShared_4439_ == 0 {
                    leanh::lean_ctor_set(v___x_4438_, 0, v___x_4441_);
                    v___x_4443_ = v___x_4438_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_4447_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4447_, 0, v___x_4441_);
                    v___x_4443_ = v_reuseFailAlloc_4447_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                if v_isShared_4433_ == 0 {
                    leanh::lean_ctor_set(v___x_4432_, 0, v___x_4443_);
                    v___x_4445_ = v___x_4432_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_4446_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4446_, 0, v___x_4443_);
                    v___x_4445_ = v_reuseFailAlloc_4446_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_4445_;
            }
            41 => {
                return v___x_4452_;
            }
            42 => {
                if v_isShared_4458_ == 0 {
                    v___x_4460_ = v___x_4457_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_4461_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4461_, 0, v_a_4455_);
                    v___x_4460_ = v_reuseFailAlloc_4461_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_4460_;
            }
            44 => {
                v___x_4473_ = lean_ptr_addr(v_k_4467_);
                v___x_4474_ = lean_ptr_addr(v_a_4469_);
                v___x_4475_ = lean_usize_dec_eq(v___x_4473_, v___x_4474_);
                if v___x_4475_ == 0 {
                    leanh::lean_inc(v_y_4466_);
                    leanh::lean_inc(v_i_4465_);
                    leanh::lean_inc(v_fvarId_4464_);
                    v_isSharedCheck_4485_ = (!leanh::lean_is_exclusive(v_code_4213_)) as u8;
                    if v_isSharedCheck_4485_ == 0 {
                        v_unused_4486_ = leanh::lean_ctor_get(v_code_4213_, 3);
                        leanh::lean_dec(v_unused_4486_);
                        v_unused_4487_ = leanh::lean_ctor_get(v_code_4213_, 2);
                        leanh::lean_dec(v_unused_4487_);
                        v_unused_4488_ = leanh::lean_ctor_get(v_code_4213_, 1);
                        leanh::lean_dec(v_unused_4488_);
                        v_unused_4489_ = leanh::lean_ctor_get(v_code_4213_, 0);
                        leanh::lean_dec(v_unused_4489_);
                        v___x_4477_ = v_code_4213_;
                        v_isShared_4478_ = v_isSharedCheck_4485_;
                        state = 45;
                        continue;
                    } else {
                        leanh::lean_dec(v_code_4213_);
                        v___x_4477_ = leanh::lean_box(0);
                        v_isShared_4478_ = v_isSharedCheck_4485_;
                        state = 45;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4469_);
                    if v_isShared_4472_ == 0 {
                        leanh::lean_ctor_set(v___x_4471_, 0, v_code_4213_);
                        v___x_4491_ = v___x_4471_;
                        state = 48;
                        continue;
                    } else {
                        v_reuseFailAlloc_4492_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4492_, 0, v_code_4213_);
                        v___x_4491_ = v_reuseFailAlloc_4492_;
                        state = 48;
                        continue;
                    }
                }
            }
            45 => {
                if v_isShared_4478_ == 0 {
                    leanh::lean_ctor_set(v___x_4477_, 3, v_a_4469_);
                    v___x_4480_ = v___x_4477_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_4484_ = leanh::lean_alloc_ctor(7, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_fvarId_4464_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4484_, 1, v_i_4465_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4484_, 2, v_y_4466_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4484_, 3, v_a_4469_);
                    v___x_4480_ = v_reuseFailAlloc_4484_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                if v_isShared_4472_ == 0 {
                    leanh::lean_ctor_set(v___x_4471_, 0, v___x_4480_);
                    v___x_4482_ = v___x_4471_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_4483_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4483_, 0, v___x_4480_);
                    v___x_4482_ = v_reuseFailAlloc_4483_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_4482_;
            }
            48 => {
                return v___x_4491_;
            }
            49 => {
                v___x_4503_ = lean_ptr_addr(v_k_4497_);
                v___x_4504_ = lean_ptr_addr(v_a_4499_);
                v___x_4505_ = lean_usize_dec_eq(v___x_4503_, v___x_4504_);
                if v___x_4505_ == 0 {
                    leanh::lean_inc(v_y_4496_);
                    leanh::lean_inc(v_i_4495_);
                    leanh::lean_inc(v_fvarId_4494_);
                    v_isSharedCheck_4515_ = (!leanh::lean_is_exclusive(v_code_4213_)) as u8;
                    if v_isSharedCheck_4515_ == 0 {
                        v_unused_4516_ = leanh::lean_ctor_get(v_code_4213_, 3);
                        leanh::lean_dec(v_unused_4516_);
                        v_unused_4517_ = leanh::lean_ctor_get(v_code_4213_, 2);
                        leanh::lean_dec(v_unused_4517_);
                        v_unused_4518_ = leanh::lean_ctor_get(v_code_4213_, 1);
                        leanh::lean_dec(v_unused_4518_);
                        v_unused_4519_ = leanh::lean_ctor_get(v_code_4213_, 0);
                        leanh::lean_dec(v_unused_4519_);
                        v___x_4507_ = v_code_4213_;
                        v_isShared_4508_ = v_isSharedCheck_4515_;
                        state = 50;
                        continue;
                    } else {
                        leanh::lean_dec(v_code_4213_);
                        v___x_4507_ = leanh::lean_box(0);
                        v_isShared_4508_ = v_isSharedCheck_4515_;
                        state = 50;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4499_);
                    if v_isShared_4502_ == 0 {
                        leanh::lean_ctor_set(v___x_4501_, 0, v_code_4213_);
                        v___x_4521_ = v___x_4501_;
                        state = 53;
                        continue;
                    } else {
                        v_reuseFailAlloc_4522_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4522_, 0, v_code_4213_);
                        v___x_4521_ = v_reuseFailAlloc_4522_;
                        state = 53;
                        continue;
                    }
                }
            }
            50 => {
                if v_isShared_4508_ == 0 {
                    leanh::lean_ctor_set(v___x_4507_, 3, v_a_4499_);
                    v___x_4510_ = v___x_4507_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_4514_ = leanh::lean_alloc_ctor(8, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_fvarId_4494_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4514_, 1, v_i_4495_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4514_, 2, v_y_4496_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4514_, 3, v_a_4499_);
                    v___x_4510_ = v_reuseFailAlloc_4514_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                if v_isShared_4502_ == 0 {
                    leanh::lean_ctor_set(v___x_4501_, 0, v___x_4510_);
                    v___x_4512_ = v___x_4501_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_4513_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4513_, 0, v___x_4510_);
                    v___x_4512_ = v_reuseFailAlloc_4513_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_4512_;
            }
            53 => {
                return v___x_4521_;
            }
            54 => {
                v___x_4535_ = lean_ptr_addr(v_k_4529_);
                v___x_4536_ = lean_ptr_addr(v_a_4531_);
                v___x_4537_ = lean_usize_dec_eq(v___x_4535_, v___x_4536_);
                if v___x_4537_ == 0 {
                    leanh::lean_inc_ref(v_ty_4528_);
                    leanh::lean_inc(v_y_4527_);
                    leanh::lean_inc(v_offset_4526_);
                    leanh::lean_inc(v_i_4525_);
                    leanh::lean_inc(v_fvarId_4524_);
                    v_isSharedCheck_4547_ = (!leanh::lean_is_exclusive(v_code_4213_)) as u8;
                    if v_isSharedCheck_4547_ == 0 {
                        v_unused_4548_ = leanh::lean_ctor_get(v_code_4213_, 5);
                        leanh::lean_dec(v_unused_4548_);
                        v_unused_4549_ = leanh::lean_ctor_get(v_code_4213_, 4);
                        leanh::lean_dec(v_unused_4549_);
                        v_unused_4550_ = leanh::lean_ctor_get(v_code_4213_, 3);
                        leanh::lean_dec(v_unused_4550_);
                        v_unused_4551_ = leanh::lean_ctor_get(v_code_4213_, 2);
                        leanh::lean_dec(v_unused_4551_);
                        v_unused_4552_ = leanh::lean_ctor_get(v_code_4213_, 1);
                        leanh::lean_dec(v_unused_4552_);
                        v_unused_4553_ = leanh::lean_ctor_get(v_code_4213_, 0);
                        leanh::lean_dec(v_unused_4553_);
                        v___x_4539_ = v_code_4213_;
                        v_isShared_4540_ = v_isSharedCheck_4547_;
                        state = 55;
                        continue;
                    } else {
                        leanh::lean_dec(v_code_4213_);
                        v___x_4539_ = leanh::lean_box(0);
                        v_isShared_4540_ = v_isSharedCheck_4547_;
                        state = 55;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4531_);
                    if v_isShared_4534_ == 0 {
                        leanh::lean_ctor_set(v___x_4533_, 0, v_code_4213_);
                        v___x_4555_ = v___x_4533_;
                        state = 58;
                        continue;
                    } else {
                        v_reuseFailAlloc_4556_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4556_, 0, v_code_4213_);
                        v___x_4555_ = v_reuseFailAlloc_4556_;
                        state = 58;
                        continue;
                    }
                }
            }
            55 => {
                if v_isShared_4540_ == 0 {
                    leanh::lean_ctor_set(v___x_4539_, 5, v_a_4531_);
                    v___x_4542_ = v___x_4539_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_4546_ = leanh::lean_alloc_ctor(9, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4546_, 0, v_fvarId_4524_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4546_, 1, v_i_4525_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4546_, 2, v_offset_4526_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4546_, 3, v_y_4527_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4546_, 4, v_ty_4528_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4546_, 5, v_a_4531_);
                    v___x_4542_ = v_reuseFailAlloc_4546_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                if v_isShared_4534_ == 0 {
                    leanh::lean_ctor_set(v___x_4533_, 0, v___x_4542_);
                    v___x_4544_ = v___x_4533_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_4545_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4545_, 0, v___x_4542_);
                    v___x_4544_ = v_reuseFailAlloc_4545_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                return v___x_4544_;
            }
            58 => {
                return v___x_4555_;
            }
            59 => {
                v___x_4566_ = lean_ptr_addr(v_k_4560_);
                v___x_4567_ = lean_ptr_addr(v_a_4562_);
                v___x_4568_ = lean_usize_dec_eq(v___x_4566_, v___x_4567_);
                if v___x_4568_ == 0 {
                    leanh::lean_inc(v_cidx_4559_);
                    leanh::lean_inc(v_fvarId_4558_);
                    v_isSharedCheck_4578_ = (!leanh::lean_is_exclusive(v_code_4213_)) as u8;
                    if v_isSharedCheck_4578_ == 0 {
                        v_unused_4579_ = leanh::lean_ctor_get(v_code_4213_, 2);
                        leanh::lean_dec(v_unused_4579_);
                        v_unused_4580_ = leanh::lean_ctor_get(v_code_4213_, 1);
                        leanh::lean_dec(v_unused_4580_);
                        v_unused_4581_ = leanh::lean_ctor_get(v_code_4213_, 0);
                        leanh::lean_dec(v_unused_4581_);
                        v___x_4570_ = v_code_4213_;
                        v_isShared_4571_ = v_isSharedCheck_4578_;
                        state = 60;
                        continue;
                    } else {
                        leanh::lean_dec(v_code_4213_);
                        v___x_4570_ = leanh::lean_box(0);
                        v_isShared_4571_ = v_isSharedCheck_4578_;
                        state = 60;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4562_);
                    if v_isShared_4565_ == 0 {
                        leanh::lean_ctor_set(v___x_4564_, 0, v_code_4213_);
                        v___x_4583_ = v___x_4564_;
                        state = 63;
                        continue;
                    } else {
                        v_reuseFailAlloc_4584_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4584_, 0, v_code_4213_);
                        v___x_4583_ = v_reuseFailAlloc_4584_;
                        state = 63;
                        continue;
                    }
                }
            }
            60 => {
                if v_isShared_4571_ == 0 {
                    leanh::lean_ctor_set(v___x_4570_, 2, v_a_4562_);
                    v___x_4573_ = v___x_4570_;
                    state = 61;
                    continue;
                } else {
                    v_reuseFailAlloc_4577_ = leanh::lean_alloc_ctor(10, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_fvarId_4558_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4577_, 1, v_cidx_4559_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4577_, 2, v_a_4562_);
                    v___x_4573_ = v_reuseFailAlloc_4577_;
                    state = 61;
                    continue;
                }
            }
            61 => {
                if v_isShared_4565_ == 0 {
                    leanh::lean_ctor_set(v___x_4564_, 0, v___x_4573_);
                    v___x_4575_ = v___x_4564_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_4576_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4576_, 0, v___x_4573_);
                    v___x_4575_ = v_reuseFailAlloc_4576_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                return v___x_4575_;
            }
            63 => {
                return v___x_4583_;
            }
            64 => {
                v___x_4596_ = lean_ptr_addr(v_k_4590_);
                v___x_4597_ = lean_ptr_addr(v_a_4592_);
                v___x_4598_ = lean_usize_dec_eq(v___x_4596_, v___x_4597_);
                if v___x_4598_ == 0 {
                    leanh::lean_inc(v_n_4587_);
                    leanh::lean_inc(v_fvarId_4586_);
                    v_isSharedCheck_4608_ = (!leanh::lean_is_exclusive(v_code_4213_)) as u8;
                    if v_isSharedCheck_4608_ == 0 {
                        v_unused_4609_ = leanh::lean_ctor_get(v_code_4213_, 2);
                        leanh::lean_dec(v_unused_4609_);
                        v_unused_4610_ = leanh::lean_ctor_get(v_code_4213_, 1);
                        leanh::lean_dec(v_unused_4610_);
                        v_unused_4611_ = leanh::lean_ctor_get(v_code_4213_, 0);
                        leanh::lean_dec(v_unused_4611_);
                        v___x_4600_ = v_code_4213_;
                        v_isShared_4601_ = v_isSharedCheck_4608_;
                        state = 65;
                        continue;
                    } else {
                        leanh::lean_dec(v_code_4213_);
                        v___x_4600_ = leanh::lean_box(0);
                        v_isShared_4601_ = v_isSharedCheck_4608_;
                        state = 65;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4592_);
                    if v_isShared_4595_ == 0 {
                        leanh::lean_ctor_set(v___x_4594_, 0, v_code_4213_);
                        v___x_4613_ = v___x_4594_;
                        state = 68;
                        continue;
                    } else {
                        v_reuseFailAlloc_4614_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4614_, 0, v_code_4213_);
                        v___x_4613_ = v_reuseFailAlloc_4614_;
                        state = 68;
                        continue;
                    }
                }
            }
            65 => {
                if v_isShared_4601_ == 0 {
                    leanh::lean_ctor_set(v___x_4600_, 2, v_a_4592_);
                    v___x_4603_ = v___x_4600_;
                    state = 66;
                    continue;
                } else {
                    v_reuseFailAlloc_4607_ = leanh::lean_alloc_ctor(11, 3, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4607_, 0, v_fvarId_4586_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4607_, 1, v_n_4587_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4607_, 2, v_a_4592_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4607_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_check_4588_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4607_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                        v_persistent_4589_,
                    );
                    v___x_4603_ = v_reuseFailAlloc_4607_;
                    state = 66;
                    continue;
                }
            }
            66 => {
                if v_isShared_4595_ == 0 {
                    leanh::lean_ctor_set(v___x_4594_, 0, v___x_4603_);
                    v___x_4605_ = v___x_4594_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_4606_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4606_, 0, v___x_4603_);
                    v___x_4605_ = v_reuseFailAlloc_4606_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_4605_;
            }
            68 => {
                return v___x_4613_;
            }
            69 => {
                v___x_4628_ = lean_ptr_addr(v_k_4621_);
                v___x_4629_ = lean_ptr_addr(v_a_4624_);
                v___x_4630_ = lean_usize_dec_eq(v___x_4628_, v___x_4629_);
                if v___x_4630_ == 0 {
                    leanh::lean_inc(v_objs_x3f_4620_);
                    leanh::lean_inc(v_n_4617_);
                    leanh::lean_inc(v_fvarId_4616_);
                    v_isSharedCheck_4640_ = (!leanh::lean_is_exclusive(v_code_4213_)) as u8;
                    if v_isSharedCheck_4640_ == 0 {
                        v_unused_4641_ = leanh::lean_ctor_get(v_code_4213_, 3);
                        leanh::lean_dec(v_unused_4641_);
                        v_unused_4642_ = leanh::lean_ctor_get(v_code_4213_, 2);
                        leanh::lean_dec(v_unused_4642_);
                        v_unused_4643_ = leanh::lean_ctor_get(v_code_4213_, 1);
                        leanh::lean_dec(v_unused_4643_);
                        v_unused_4644_ = leanh::lean_ctor_get(v_code_4213_, 0);
                        leanh::lean_dec(v_unused_4644_);
                        v___x_4632_ = v_code_4213_;
                        v_isShared_4633_ = v_isSharedCheck_4640_;
                        state = 70;
                        continue;
                    } else {
                        leanh::lean_dec(v_code_4213_);
                        v___x_4632_ = leanh::lean_box(0);
                        v_isShared_4633_ = v_isSharedCheck_4640_;
                        state = 70;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4624_);
                    if v_isShared_4627_ == 0 {
                        leanh::lean_ctor_set(v___x_4626_, 0, v_code_4213_);
                        v___x_4646_ = v___x_4626_;
                        state = 73;
                        continue;
                    } else {
                        v_reuseFailAlloc_4647_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4647_, 0, v_code_4213_);
                        v___x_4646_ = v_reuseFailAlloc_4647_;
                        state = 73;
                        continue;
                    }
                }
            }
            70 => {
                if v_isShared_4633_ == 0 {
                    leanh::lean_ctor_set(v___x_4632_, 3, v_a_4624_);
                    v___x_4635_ = v___x_4632_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_4639_ = leanh::lean_alloc_ctor(12, 4, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4639_, 0, v_fvarId_4616_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4639_, 1, v_n_4617_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4639_, 2, v_objs_x3f_4620_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4639_, 3, v_a_4624_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4639_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        v_check_4618_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4639_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
                        v_persistent_4619_,
                    );
                    v___x_4635_ = v_reuseFailAlloc_4639_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                if v_isShared_4627_ == 0 {
                    leanh::lean_ctor_set(v___x_4626_, 0, v___x_4635_);
                    v___x_4637_ = v___x_4626_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_4638_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4638_, 0, v___x_4635_);
                    v___x_4637_ = v_reuseFailAlloc_4638_;
                    state = 72;
                    continue;
                }
            }
            72 => {
                return v___x_4637_;
            }
            73 => {
                return v___x_4646_;
            }
            74 => {
                v___x_4662_ = lean_ptr_addr(v_k_4656_);
                v___x_4663_ = lean_ptr_addr(v_a_4658_);
                v___x_4664_ = lean_usize_dec_eq(v___x_4662_, v___x_4663_);
                if v___x_4664_ == 0 {
                    leanh::lean_inc(v_fvarId_4655_);
                    v_isSharedCheck_4674_ = (!leanh::lean_is_exclusive(v_code_4213_)) as u8;
                    if v_isSharedCheck_4674_ == 0 {
                        v_unused_4675_ = leanh::lean_ctor_get(v_code_4213_, 1);
                        leanh::lean_dec(v_unused_4675_);
                        v_unused_4676_ = leanh::lean_ctor_get(v_code_4213_, 0);
                        leanh::lean_dec(v_unused_4676_);
                        v___x_4666_ = v_code_4213_;
                        v_isShared_4667_ = v_isSharedCheck_4674_;
                        state = 75;
                        continue;
                    } else {
                        leanh::lean_dec(v_code_4213_);
                        v___x_4666_ = leanh::lean_box(0);
                        v_isShared_4667_ = v_isSharedCheck_4674_;
                        state = 75;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4658_);
                    if v_isShared_4661_ == 0 {
                        leanh::lean_ctor_set(v___x_4660_, 0, v_code_4213_);
                        v___x_4678_ = v___x_4660_;
                        state = 78;
                        continue;
                    } else {
                        v_reuseFailAlloc_4679_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4679_, 0, v_code_4213_);
                        v___x_4678_ = v_reuseFailAlloc_4679_;
                        state = 78;
                        continue;
                    }
                }
            }
            75 => {
                if v_isShared_4667_ == 0 {
                    leanh::lean_ctor_set(v___x_4666_, 1, v_a_4658_);
                    v___x_4669_ = v___x_4666_;
                    state = 76;
                    continue;
                } else {
                    v_reuseFailAlloc_4673_ = leanh::lean_alloc_ctor(13, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4673_, 0, v_fvarId_4655_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4673_, 1, v_a_4658_);
                    v___x_4669_ = v_reuseFailAlloc_4673_;
                    state = 76;
                    continue;
                }
            }
            76 => {
                if v_isShared_4661_ == 0 {
                    leanh::lean_ctor_set(v___x_4660_, 0, v___x_4669_);
                    v___x_4671_ = v___x_4660_;
                    state = 77;
                    continue;
                } else {
                    v_reuseFailAlloc_4672_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4672_, 0, v___x_4669_);
                    v___x_4671_ = v_reuseFailAlloc_4672_;
                    state = 77;
                    continue;
                }
            }
            77 => {
                return v___x_4671_;
            }
            78 => {
                return v___x_4678_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0(
    mut v_resetTokenId_4682_: *mut leanh::LeanObject,
    mut v_origAllocId_4683_: *mut leanh::LeanObject,
    mut v_isSharedId_4684_: *mut leanh::LeanObject,
    mut v_resultType_4685_: *mut leanh::LeanObject,
    mut v_x_4686_: *mut leanh::LeanObject,
    mut v___y_4687_: *mut leanh::LeanObject,
    mut v___y_4688_: *mut leanh::LeanObject,
    mut v___y_4689_: *mut leanh::LeanObject,
    mut v___y_4690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4692_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(
            v_resetTokenId_4682_,
            v_x_4686_,
            v_origAllocId_4683_,
            v_isSharedId_4684_,
            v_resultType_4685_,
            v___y_4687_,
            v___y_4688_,
            v___y_4689_,
            v___y_4690_,
        );
    return v___x_4692_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___boxed(
    mut v_resetTokenId_4693_: *mut leanh::LeanObject,
    mut v_origAllocId_4694_: *mut leanh::LeanObject,
    mut v_isSharedId_4695_: *mut leanh::LeanObject,
    mut v_resultType_4696_: *mut leanh::LeanObject,
    mut v_i_4697_: *mut leanh::LeanObject,
    mut v_as_4698_: *mut leanh::LeanObject,
    mut v___y_4699_: *mut leanh::LeanObject,
    mut v___y_4700_: *mut leanh::LeanObject,
    mut v___y_4701_: *mut leanh::LeanObject,
    mut v___y_4702_: *mut leanh::LeanObject,
    mut v___y_4703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4704_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(v_resetTokenId_4693_, v_origAllocId_4694_, v_isSharedId_4695_, v_resultType_4696_, v_i_4697_, v_as_4698_, v___y_4699_, v___y_4700_, v___y_4701_, v___y_4702_);
    leanh::lean_dec(v___y_4702_);
    leanh::lean_dec_ref(v___y_4701_);
    leanh::lean_dec(v___y_4700_);
    leanh::lean_dec_ref(v___y_4699_);
    return v_res_4704_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___boxed(
    mut v_resetTokenId_4705_: *mut leanh::LeanObject,
    mut v_code_4706_: *mut leanh::LeanObject,
    mut v_origAllocId_4707_: *mut leanh::LeanObject,
    mut v_isSharedId_4708_: *mut leanh::LeanObject,
    mut v_currentRetType_4709_: *mut leanh::LeanObject,
    mut v_a_4710_: *mut leanh::LeanObject,
    mut v_a_4711_: *mut leanh::LeanObject,
    mut v_a_4712_: *mut leanh::LeanObject,
    mut v_a_4713_: *mut leanh::LeanObject,
    mut v_a_4714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4715_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(
            v_resetTokenId_4705_,
            v_code_4706_,
            v_origAllocId_4707_,
            v_isSharedId_4708_,
            v_currentRetType_4709_,
            v_a_4710_,
            v_a_4711_,
            v_a_4712_,
            v_a_4713_,
        );
    leanh::lean_dec(v_a_4713_);
    leanh::lean_dec_ref(v_a_4712_);
    leanh::lean_dec(v_a_4711_);
    leanh::lean_dec_ref(v_a_4710_);
    return v_res_4715_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(
    mut v_currentRetType_4725_: *mut leanh::LeanObject,
    mut v_ds_4726_: *mut leanh::LeanObject,
    mut v_decl_4727_: *mut leanh::LeanObject,
    mut v_nFields_4728_: *mut leanh::LeanObject,
    mut v_origAllocId_4729_: *mut leanh::LeanObject,
    mut v_k_4730_: *mut leanh::LeanObject,
    mut v_a_4731_: *mut leanh::LeanObject,
    mut v_a_4732_: *mut leanh::LeanObject,
    mut v_a_4733_: *mut leanh::LeanObject,
    mut v_a_4734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4742_: u8 = 0;
    let mut v___x_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: u8 = 0;
    let mut v___x_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: u8 = 0;
    let mut v___x_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_4752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4761_: u8 = 0;
    let mut v___x_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4791_: u8 = 0;
    let mut v___x_4793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4800_: u8 = 0;
    let mut v_unused_4801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4805_: u8 = 0;
    let mut v___x_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4809_: u8 = 0;
    let mut v_a_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4813_: u8 = 0;
    let mut v___x_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4817_: u8 = 0;
    let mut v_reuseFailAlloc_4818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4822_: u8 = 0;
    let mut v___x_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4826_: u8 = 0;
    let mut v_a_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4830_: u8 = 0;
    let mut v___x_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4834_: u8 = 0;
    let mut v_a_4835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4838_: u8 = 0;
    let mut v___x_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4842_: u8 = 0;
    let mut v_isSharedCheck_4843_: u8 = 0;
    let mut v_a_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4847_: u8 = 0;
    let mut v___x_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4851_: u8 = 0;
    let mut v_a_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4855_: u8 = 0;
    let mut v___x_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4859_: u8 = 0;
    let mut v_isSharedCheck_4860_: u8 = 0;
    let mut v_a_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4864_: u8 = 0;
    let mut v___x_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4868_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4736_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(v_nFields_4728_, v_origAllocId_4729_, v_ds_4726_, v_a_4731_, v_a_4732_, v_a_4733_, v_a_4734_);
                if leanh::lean_obj_tag(v___x_4736_) == 0 {
                    v_a_4737_ = leanh::lean_ctor_get(v___x_4736_, 0);
                    leanh::lean_inc(v_a_4737_);
                    leanh::lean_dec_ref_known(v___x_4736_, 1);
                    v_fst_4738_ = leanh::lean_ctor_get(v_a_4737_, 0);
                    v_snd_4739_ = leanh::lean_ctor_get(v_a_4737_, 1);
                    v_isSharedCheck_4860_ = (!leanh::lean_is_exclusive(v_a_4737_)) as u8;
                    if v_isSharedCheck_4860_ == 0 {
                        v___x_4741_ = v_a_4737_;
                        v_isShared_4742_ = v_isSharedCheck_4860_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4739_);
                        leanh::lean_inc(v_fst_4738_);
                        leanh::lean_dec(v_a_4737_);
                        v___x_4741_ = leanh::lean_box(0);
                        v_isShared_4742_ = v_isSharedCheck_4860_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_k_4730_);
                    leanh::lean_dec(v_origAllocId_4729_);
                    leanh::lean_dec_ref(v_decl_4727_);
                    leanh::lean_dec_ref(v_currentRetType_4725_);
                    v_a_4861_ = leanh::lean_ctor_get(v___x_4736_, 0);
                    v_isSharedCheck_4868_ = (!leanh::lean_is_exclusive(v___x_4736_)) as u8;
                    if v_isSharedCheck_4868_ == 0 {
                        v___x_4863_ = v___x_4736_;
                        v_isShared_4864_ = v_isSharedCheck_4868_;
                        state = 21;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4861_);
                        leanh::lean_dec(v___x_4736_);
                        v___x_4863_ = leanh::lean_box(0);
                        v_isShared_4864_ = v_isSharedCheck_4868_;
                        state = 21;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4743_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__1;
                v___x_4744_ =
                    l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4743_, v_a_4732_);
                if leanh::lean_obj_tag(v___x_4744_) == 0 {
                    v_a_4745_ = leanh::lean_ctor_get(v___x_4744_, 0);
                    leanh::lean_inc(v_a_4745_);
                    leanh::lean_dec_ref_known(v___x_4744_, 1);
                    v___x_4746_ = 1;
                    v___x_4747_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4_once), _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4);
                    v___x_4748_ = 0;
                    v___x_4749_ = l_Lean_Compiler_LCNF_mkParam(
                        v___x_4746_,
                        v_a_4745_,
                        v___x_4747_,
                        v___x_4748_,
                        v_a_4731_,
                        v_a_4732_,
                        v_a_4733_,
                        v_a_4734_,
                    );
                    if leanh::lean_obj_tag(v___x_4749_) == 0 {
                        v_a_4750_ = leanh::lean_ctor_get(v___x_4749_, 0);
                        leanh::lean_inc(v_a_4750_);
                        leanh::lean_dec_ref_known(v___x_4749_, 1);
                        v_fvarId_4751_ = leanh::lean_ctor_get(v_decl_4727_, 0);
                        v_binderName_4752_ = leanh::lean_ctor_get(v_decl_4727_, 1);
                        v_fvarId_4753_ = leanh::lean_ctor_get(v_a_4750_, 0);
                        leanh::lean_inc_ref(v_currentRetType_4725_);
                        leanh::lean_inc(v_fvarId_4753_);
                        leanh::lean_inc(v_origAllocId_4729_);
                        leanh::lean_inc(v_fvarId_4751_);
                        v___x_4754_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_fvarId_4751_, v_k_4730_, v_origAllocId_4729_, v_fvarId_4753_, v_currentRetType_4725_, v_a_4731_, v_a_4732_, v_a_4733_, v_a_4734_);
                        if leanh::lean_obj_tag(v___x_4754_) == 0 {
                            v_a_4755_ = leanh::lean_ctor_get(v___x_4754_, 0);
                            leanh::lean_inc(v_a_4755_);
                            leanh::lean_dec_ref_known(v___x_4754_, 1);
                            v___x_4756_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0;
                            leanh::lean_inc_ref(v_currentRetType_4725_);
                            v___x_4757_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_a_4755_, v___x_4756_, v_currentRetType_4725_, v_a_4731_, v_a_4732_, v_a_4733_, v_a_4734_);
                            if leanh::lean_obj_tag(v___x_4757_) == 0 {
                                v_a_4758_ = leanh::lean_ctor_get(v___x_4757_, 0);
                                v_isSharedCheck_4843_ =
                                    (!leanh::lean_is_exclusive(v___x_4757_)) as u8;
                                if v_isSharedCheck_4843_ == 0 {
                                    v___x_4760_ = v___x_4757_;
                                    v_isShared_4761_ = v_isSharedCheck_4843_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4758_);
                                    leanh::lean_dec(v___x_4757_);
                                    v___x_4760_ = leanh::lean_box(0);
                                    v_isShared_4761_ = v_isSharedCheck_4843_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_4750_);
                                leanh::lean_del_object(v___x_4741_);
                                leanh::lean_dec(v_snd_4739_);
                                leanh::lean_dec(v_fst_4738_);
                                leanh::lean_dec(v_origAllocId_4729_);
                                leanh::lean_dec_ref(v_decl_4727_);
                                leanh::lean_dec_ref(v_currentRetType_4725_);
                                return v___x_4757_;
                            }
                        } else {
                            leanh::lean_dec(v_a_4750_);
                            leanh::lean_del_object(v___x_4741_);
                            leanh::lean_dec(v_snd_4739_);
                            leanh::lean_dec(v_fst_4738_);
                            leanh::lean_dec(v_origAllocId_4729_);
                            leanh::lean_dec_ref(v_decl_4727_);
                            leanh::lean_dec_ref(v_currentRetType_4725_);
                            return v___x_4754_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_4741_);
                        leanh::lean_dec(v_snd_4739_);
                        leanh::lean_dec(v_fst_4738_);
                        leanh::lean_dec_ref(v_k_4730_);
                        leanh::lean_dec(v_origAllocId_4729_);
                        leanh::lean_dec_ref(v_decl_4727_);
                        leanh::lean_dec_ref(v_currentRetType_4725_);
                        v_a_4844_ = leanh::lean_ctor_get(v___x_4749_, 0);
                        v_isSharedCheck_4851_ =
                            (!leanh::lean_is_exclusive(v___x_4749_)) as u8;
                        if v_isSharedCheck_4851_ == 0 {
                            v___x_4846_ = v___x_4749_;
                            v_isShared_4847_ = v_isSharedCheck_4851_;
                            state = 17;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4844_);
                            leanh::lean_dec(v___x_4749_);
                            v___x_4846_ = leanh::lean_box(0);
                            v_isShared_4847_ = v_isSharedCheck_4851_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_4741_);
                    leanh::lean_dec(v_snd_4739_);
                    leanh::lean_dec(v_fst_4738_);
                    leanh::lean_dec_ref(v_k_4730_);
                    leanh::lean_dec(v_origAllocId_4729_);
                    leanh::lean_dec_ref(v_decl_4727_);
                    leanh::lean_dec_ref(v_currentRetType_4725_);
                    v_a_4852_ = leanh::lean_ctor_get(v___x_4744_, 0);
                    v_isSharedCheck_4859_ = (!leanh::lean_is_exclusive(v___x_4744_)) as u8;
                    if v_isSharedCheck_4859_ == 0 {
                        v___x_4854_ = v___x_4744_;
                        v_isShared_4855_ = v_isSharedCheck_4859_;
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4852_);
                        leanh::lean_dec(v___x_4744_);
                        v___x_4854_ = leanh::lean_box(0);
                        v_isShared_4855_ = v_isSharedCheck_4859_;
                        state = 19;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4762_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__3;
                v___x_4763_ =
                    l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4762_, v_a_4732_);
                if leanh::lean_obj_tag(v___x_4763_) == 0 {
                    v_a_4764_ = leanh::lean_ctor_get(v___x_4763_, 0);
                    leanh::lean_inc(v_a_4764_);
                    leanh::lean_dec_ref_known(v___x_4763_, 1);
                    v___x_4765_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4);
                    leanh::lean_inc(v_binderName_4752_);
                    leanh::lean_inc(v_fvarId_4751_);
                    v___x_4766_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v___x_4766_, 0, v_fvarId_4751_);
                    leanh::lean_ctor_set(v___x_4766_, 1, v_binderName_4752_);
                    leanh::lean_ctor_set(v___x_4766_, 2, v___x_4765_);
                    leanh::lean_ctor_set_uint8(
                        v___x_4766_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v___x_4748_,
                    );
                    v___x_4767_ = leanh::lean_unsigned_to_nat(2);
                    v___x_4768_ = lean_mk_empty_array_with_capacity(v___x_4767_);
                    v___x_4769_ = lean_array_push(v___x_4768_, v___x_4766_);
                    v___x_4770_ = lean_array_push(v___x_4769_, v_a_4750_);
                    leanh::lean_inc_ref(v_currentRetType_4725_);
                    v___x_4771_ = l_Lean_Compiler_LCNF_mkFunDecl(
                        v___x_4746_,
                        v_a_4764_,
                        v_currentRetType_4725_,
                        v___x_4770_,
                        v_a_4758_,
                        v_a_4731_,
                        v_a_4732_,
                        v_a_4733_,
                        v_a_4734_,
                    );
                    if leanh::lean_obj_tag(v___x_4771_) == 0 {
                        v_a_4772_ = leanh::lean_ctor_get(v___x_4771_, 0);
                        leanh::lean_inc(v_a_4772_);
                        leanh::lean_dec_ref_known(v___x_4771_, 1);
                        v___x_4773_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__5;
                        v___x_4774_ =
                            l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4773_, v_a_4732_);
                        if leanh::lean_obj_tag(v___x_4774_) == 0 {
                            v_a_4775_ = leanh::lean_ctor_get(v___x_4774_, 0);
                            leanh::lean_inc(v_a_4775_);
                            leanh::lean_dec_ref_known(v___x_4774_, 1);
                            leanh::lean_inc(v_origAllocId_4729_);
                            if v_isShared_4761_ == 0 {
                                leanh::lean_ctor_set_tag(v___x_4760_, 15);
                                leanh::lean_ctor_set(v___x_4760_, 0, v_origAllocId_4729_);
                                v___x_4777_ = v___x_4760_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_4818_ =
                                    leanh::lean_alloc_ctor(15, 1, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4818_,
                                    0,
                                    v_origAllocId_4729_,
                                );
                                v___x_4777_ = v_reuseFailAlloc_4818_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_4772_);
                            leanh::lean_del_object(v___x_4760_);
                            leanh::lean_del_object(v___x_4741_);
                            leanh::lean_dec(v_snd_4739_);
                            leanh::lean_dec(v_fst_4738_);
                            leanh::lean_dec(v_origAllocId_4729_);
                            leanh::lean_dec_ref(v_decl_4727_);
                            leanh::lean_dec_ref(v_currentRetType_4725_);
                            v_a_4819_ = leanh::lean_ctor_get(v___x_4774_, 0);
                            v_isSharedCheck_4826_ =
                                (!leanh::lean_is_exclusive(v___x_4774_)) as u8;
                            if v_isSharedCheck_4826_ == 0 {
                                v___x_4821_ = v___x_4774_;
                                v_isShared_4822_ = v_isSharedCheck_4826_;
                                state = 11;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4819_);
                                leanh::lean_dec(v___x_4774_);
                                v___x_4821_ = leanh::lean_box(0);
                                v_isShared_4822_ = v_isSharedCheck_4826_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_del_object(v___x_4760_);
                        leanh::lean_del_object(v___x_4741_);
                        leanh::lean_dec(v_snd_4739_);
                        leanh::lean_dec(v_fst_4738_);
                        leanh::lean_dec(v_origAllocId_4729_);
                        leanh::lean_dec_ref(v_decl_4727_);
                        leanh::lean_dec_ref(v_currentRetType_4725_);
                        v_a_4827_ = leanh::lean_ctor_get(v___x_4771_, 0);
                        v_isSharedCheck_4834_ =
                            (!leanh::lean_is_exclusive(v___x_4771_)) as u8;
                        if v_isSharedCheck_4834_ == 0 {
                            v___x_4829_ = v___x_4771_;
                            v_isShared_4830_ = v_isSharedCheck_4834_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4827_);
                            leanh::lean_dec(v___x_4771_);
                            v___x_4829_ = leanh::lean_box(0);
                            v_isShared_4830_ = v_isSharedCheck_4834_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_4760_);
                    leanh::lean_dec(v_a_4758_);
                    leanh::lean_dec(v_a_4750_);
                    leanh::lean_del_object(v___x_4741_);
                    leanh::lean_dec(v_snd_4739_);
                    leanh::lean_dec(v_fst_4738_);
                    leanh::lean_dec(v_origAllocId_4729_);
                    leanh::lean_dec_ref(v_decl_4727_);
                    leanh::lean_dec_ref(v_currentRetType_4725_);
                    v_a_4835_ = leanh::lean_ctor_get(v___x_4763_, 0);
                    v_isSharedCheck_4842_ = (!leanh::lean_is_exclusive(v___x_4763_)) as u8;
                    if v_isSharedCheck_4842_ == 0 {
                        v___x_4837_ = v___x_4763_;
                        v_isShared_4838_ = v_isSharedCheck_4842_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4835_);
                        leanh::lean_dec(v___x_4763_);
                        v___x_4837_ = leanh::lean_box(0);
                        v_isShared_4838_ = v_isSharedCheck_4842_;
                        state = 15;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4778_ = l_Lean_Compiler_LCNF_mkLetDecl(
                    v___x_4746_,
                    v_a_4775_,
                    v___x_4747_,
                    v___x_4777_,
                    v_a_4731_,
                    v_a_4732_,
                    v_a_4733_,
                    v_a_4734_,
                );
                if leanh::lean_obj_tag(v___x_4778_) == 0 {
                    v_a_4779_ = leanh::lean_ctor_get(v___x_4778_, 0);
                    leanh::lean_inc(v_a_4779_);
                    leanh::lean_dec_ref_known(v___x_4778_, 1);
                    v_fvarId_4780_ = leanh::lean_ctor_get(v_a_4772_, 0);
                    v_fvarId_4781_ = leanh::lean_ctor_get(v_a_4779_, 0);
                    leanh::lean_inc(v_fvarId_4781_);
                    leanh::lean_inc(v_fvarId_4780_);
                    leanh::lean_inc(v_origAllocId_4729_);
                    v___x_4782_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(v_origAllocId_4729_, v_snd_4739_, v_fvarId_4780_, v_fvarId_4781_, v_a_4731_, v_a_4732_, v_a_4733_, v_a_4734_);
                    if leanh::lean_obj_tag(v___x_4782_) == 0 {
                        v_a_4783_ = leanh::lean_ctor_get(v___x_4782_, 0);
                        leanh::lean_inc(v_a_4783_);
                        leanh::lean_dec_ref_known(v___x_4782_, 1);
                        leanh::lean_inc(v_fvarId_4781_);
                        leanh::lean_inc(v_fvarId_4780_);
                        v___x_4784_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(v_origAllocId_4729_, v_snd_4739_, v_fvarId_4780_, v_fvarId_4781_, v_a_4731_, v_a_4732_, v_a_4733_, v_a_4734_);
                        leanh::lean_dec(v_snd_4739_);
                        if leanh::lean_obj_tag(v___x_4784_) == 0 {
                            v_a_4785_ = leanh::lean_ctor_get(v___x_4784_, 0);
                            leanh::lean_inc(v_a_4785_);
                            leanh::lean_dec_ref_known(v___x_4784_, 1);
                            leanh::lean_inc(v_fvarId_4781_);
                            v___x_4786_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_fvarId_4781_, v___x_4747_, v_currentRetType_4725_, v_a_4783_, v_a_4785_);
                            if leanh::lean_obj_tag(v___x_4786_) == 0 {
                                v_a_4787_ = leanh::lean_ctor_get(v___x_4786_, 0);
                                leanh::lean_inc(v_a_4787_);
                                leanh::lean_dec_ref_known(v___x_4786_, 1);
                                v___x_4788_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(
                                    v___x_4746_,
                                    v_decl_4727_,
                                    v_a_4732_,
                                );
                                leanh::lean_dec_ref(v_decl_4727_);
                                if leanh::lean_obj_tag(v___x_4788_) == 0 {
                                    v_isSharedCheck_4800_ =
                                        (!leanh::lean_is_exclusive(v___x_4788_)) as u8;
                                    if v_isSharedCheck_4800_ == 0 {
                                        v_unused_4801_ =
                                            leanh::lean_ctor_get(v___x_4788_, 0);
                                        leanh::lean_dec(v_unused_4801_);
                                        v___x_4790_ = v___x_4788_;
                                        v_isShared_4791_ = v_isSharedCheck_4800_;
                                        state = 4;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_4788_);
                                        v___x_4790_ = leanh::lean_box(0);
                                        v_isShared_4791_ = v_isSharedCheck_4800_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_4787_);
                                    leanh::lean_dec(v_a_4779_);
                                    leanh::lean_dec(v_a_4772_);
                                    leanh::lean_del_object(v___x_4741_);
                                    leanh::lean_dec(v_fst_4738_);
                                    v_a_4802_ = leanh::lean_ctor_get(v___x_4788_, 0);
                                    v_isSharedCheck_4809_ =
                                        (!leanh::lean_is_exclusive(v___x_4788_)) as u8;
                                    if v_isSharedCheck_4809_ == 0 {
                                        v___x_4804_ = v___x_4788_;
                                        v_isShared_4805_ = v_isSharedCheck_4809_;
                                        state = 7;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4802_);
                                        leanh::lean_dec(v___x_4788_);
                                        v___x_4804_ = leanh::lean_box(0);
                                        v_isShared_4805_ = v_isSharedCheck_4809_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_a_4779_);
                                leanh::lean_dec(v_a_4772_);
                                leanh::lean_del_object(v___x_4741_);
                                leanh::lean_dec(v_fst_4738_);
                                leanh::lean_dec_ref(v_decl_4727_);
                                return v___x_4786_;
                            }
                        } else {
                            leanh::lean_dec(v_a_4783_);
                            leanh::lean_dec(v_a_4779_);
                            leanh::lean_dec(v_a_4772_);
                            leanh::lean_del_object(v___x_4741_);
                            leanh::lean_dec(v_fst_4738_);
                            leanh::lean_dec_ref(v_decl_4727_);
                            leanh::lean_dec_ref(v_currentRetType_4725_);
                            return v___x_4784_;
                        }
                    } else {
                        leanh::lean_dec(v_a_4779_);
                        leanh::lean_dec(v_a_4772_);
                        leanh::lean_del_object(v___x_4741_);
                        leanh::lean_dec(v_snd_4739_);
                        leanh::lean_dec(v_fst_4738_);
                        leanh::lean_dec(v_origAllocId_4729_);
                        leanh::lean_dec_ref(v_decl_4727_);
                        leanh::lean_dec_ref(v_currentRetType_4725_);
                        return v___x_4782_;
                    }
                } else {
                    leanh::lean_dec(v_a_4772_);
                    leanh::lean_del_object(v___x_4741_);
                    leanh::lean_dec(v_snd_4739_);
                    leanh::lean_dec(v_fst_4738_);
                    leanh::lean_dec(v_origAllocId_4729_);
                    leanh::lean_dec_ref(v_decl_4727_);
                    leanh::lean_dec_ref(v_currentRetType_4725_);
                    v_a_4810_ = leanh::lean_ctor_get(v___x_4778_, 0);
                    v_isSharedCheck_4817_ = (!leanh::lean_is_exclusive(v___x_4778_)) as u8;
                    if v_isSharedCheck_4817_ == 0 {
                        v___x_4812_ = v___x_4778_;
                        v_isShared_4813_ = v_isSharedCheck_4817_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4810_);
                        leanh::lean_dec(v___x_4778_);
                        v___x_4812_ = leanh::lean_box(0);
                        v_isShared_4813_ = v_isSharedCheck_4817_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4742_ == 0 {
                    leanh::lean_ctor_set(v___x_4741_, 1, v_a_4787_);
                    leanh::lean_ctor_set(v___x_4741_, 0, v_a_4779_);
                    v___x_4793_ = v___x_4741_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4799_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_a_4779_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4799_, 1, v_a_4787_);
                    v___x_4793_ = v_reuseFailAlloc_4799_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4794_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4794_, 0, v_a_4772_);
                leanh::lean_ctor_set(v___x_4794_, 1, v___x_4793_);
                v___x_4795_ =
                    l_Lean_Compiler_LCNF_attachCodeDecls(v___x_4746_, v_fst_4738_, v___x_4794_);
                leanh::lean_dec(v_fst_4738_);
                if v_isShared_4791_ == 0 {
                    leanh::lean_ctor_set(v___x_4790_, 0, v___x_4795_);
                    v___x_4797_ = v___x_4790_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4798_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 0, v___x_4795_);
                    v___x_4797_ = v_reuseFailAlloc_4798_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4797_;
            }
            7 => {
                if v_isShared_4805_ == 0 {
                    v___x_4807_ = v___x_4804_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4808_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4808_, 0, v_a_4802_);
                    v___x_4807_ = v_reuseFailAlloc_4808_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4807_;
            }
            9 => {
                if v_isShared_4813_ == 0 {
                    v___x_4815_ = v___x_4812_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4816_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4816_, 0, v_a_4810_);
                    v___x_4815_ = v_reuseFailAlloc_4816_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4815_;
            }
            11 => {
                if v_isShared_4822_ == 0 {
                    v___x_4824_ = v___x_4821_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4825_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4825_, 0, v_a_4819_);
                    v___x_4824_ = v_reuseFailAlloc_4825_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4824_;
            }
            13 => {
                if v_isShared_4830_ == 0 {
                    v___x_4832_ = v___x_4829_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4833_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4833_, 0, v_a_4827_);
                    v___x_4832_ = v_reuseFailAlloc_4833_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4832_;
            }
            15 => {
                if v_isShared_4838_ == 0 {
                    v___x_4840_ = v___x_4837_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4841_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4841_, 0, v_a_4835_);
                    v___x_4840_ = v_reuseFailAlloc_4841_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4840_;
            }
            17 => {
                if v_isShared_4847_ == 0 {
                    v___x_4849_ = v___x_4846_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4850_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4850_, 0, v_a_4844_);
                    v___x_4849_ = v_reuseFailAlloc_4850_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4849_;
            }
            19 => {
                if v_isShared_4855_ == 0 {
                    v___x_4857_ = v___x_4854_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4858_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4858_, 0, v_a_4852_);
                    v___x_4857_ = v_reuseFailAlloc_4858_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4857_;
            }
            21 => {
                if v_isShared_4864_ == 0 {
                    v___x_4866_ = v___x_4863_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4867_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4867_, 0, v_a_4861_);
                    v___x_4866_ = v_reuseFailAlloc_4867_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4866_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0___boxed(
    mut v_resultType_4869_: *mut leanh::LeanObject,
    mut v_x_4870_: *mut leanh::LeanObject,
    mut v___y_4871_: *mut leanh::LeanObject,
    mut v___y_4872_: *mut leanh::LeanObject,
    mut v___y_4873_: *mut leanh::LeanObject,
    mut v___y_4874_: *mut leanh::LeanObject,
    mut v___y_4875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4876_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0(v_resultType_4869_, v_x_4870_, v___y_4871_, v___y_4872_, v___y_4873_, v___y_4874_);
    leanh::lean_dec(v___y_4874_);
    leanh::lean_dec_ref(v___y_4873_);
    leanh::lean_dec(v___y_4872_);
    leanh::lean_dec_ref(v___y_4871_);
    return v_res_4876_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(
    mut v_resultType_4877_: *mut leanh::LeanObject,
    mut v_i_4878_: *mut leanh::LeanObject,
    mut v_as_4879_: *mut leanh::LeanObject,
    mut v___y_4880_: *mut leanh::LeanObject,
    mut v___y_4881_: *mut leanh::LeanObject,
    mut v___y_4882_: *mut leanh::LeanObject,
    mut v___y_4883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: u8 = 0;
    let mut v___x_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: usize = 0;
    let mut v___x_4893_: usize = 0;
    let mut v___x_4894_: u8 = 0;
    let mut v___x_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4905_: u8 = 0;
    let mut v___x_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4909_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4885_ = lean_array_get_size(v_as_4879_);
                v___x_4886_ = lean_nat_dec_lt(v_i_4878_, v___x_4885_);
                if v___x_4886_ == 0 {
                    leanh::lean_dec(v_i_4878_);
                    leanh::lean_dec_ref(v_resultType_4877_);
                    v___x_4887_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4887_, 0, v_as_4879_);
                    return v___x_4887_;
                } else {
                    leanh::lean_inc_ref(v_resultType_4877_);
                    v___f_4888_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                    leanh::lean_closure_set(v___f_4888_, 0, v_resultType_4877_);
                    v_a_4889_ = lean_array_fget_borrowed(v_as_4879_, v_i_4878_);
                    leanh::lean_inc(v_a_4889_);
                    v___x_4890_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_a_4889_, v___f_4888_, v___y_4880_, v___y_4881_, v___y_4882_, v___y_4883_);
                    if leanh::lean_obj_tag(v___x_4890_) == 0 {
                        v_a_4891_ = leanh::lean_ctor_get(v___x_4890_, 0);
                        leanh::lean_inc(v_a_4891_);
                        leanh::lean_dec_ref_known(v___x_4890_, 1);
                        v___x_4892_ = lean_ptr_addr(v_a_4889_);
                        v___x_4893_ = lean_ptr_addr(v_a_4891_);
                        v___x_4894_ = lean_usize_dec_eq(v___x_4892_, v___x_4893_);
                        if v___x_4894_ == 0 {
                            v___x_4895_ = leanh::lean_unsigned_to_nat(1);
                            v___x_4896_ = lean_nat_add(v_i_4878_, v___x_4895_);
                            v___x_4897_ = lean_array_fset(v_as_4879_, v_i_4878_, v_a_4891_);
                            leanh::lean_dec(v_i_4878_);
                            v_i_4878_ = v___x_4896_;
                            v_as_4879_ = v___x_4897_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_4891_);
                            v___x_4899_ = leanh::lean_unsigned_to_nat(1);
                            v___x_4900_ = lean_nat_add(v_i_4878_, v___x_4899_);
                            leanh::lean_dec(v_i_4878_);
                            v_i_4878_ = v___x_4900_;
                            state = 0;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_as_4879_);
                        leanh::lean_dec(v_i_4878_);
                        leanh::lean_dec_ref(v_resultType_4877_);
                        v_a_4902_ = leanh::lean_ctor_get(v___x_4890_, 0);
                        v_isSharedCheck_4909_ =
                            (!leanh::lean_is_exclusive(v___x_4890_)) as u8;
                        if v_isSharedCheck_4909_ == 0 {
                            v___x_4904_ = v___x_4890_;
                            v_isShared_4905_ = v_isSharedCheck_4909_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4902_);
                            leanh::lean_dec(v___x_4890_);
                            v___x_4904_ = leanh::lean_box(0);
                            v_isShared_4905_ = v_isSharedCheck_4909_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4905_ == 0 {
                    v___x_4907_ = v___x_4904_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4908_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 0, v_a_4902_);
                    v___x_4907_ = v_reuseFailAlloc_4908_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4907_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(
    mut v_code_4910_: *mut leanh::LeanObject,
    mut v_ds_4911_: *mut leanh::LeanObject,
    mut v_currentRetType_4912_: *mut leanh::LeanObject,
    mut v_a_4913_: *mut leanh::LeanObject,
    mut v_a_4914_: *mut leanh::LeanObject,
    mut v_a_4915_: *mut leanh::LeanObject,
    mut v_a_4916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_code_4919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ds_4920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: u8 = 0;
    let mut v_d_4927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_4930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_4934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4947_: u8 = 0;
    let mut v___x_4948_: u8 = 0;
    let mut v___x_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4959_: u8 = 0;
    let mut v___x_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4963_: u8 = 0;
    let mut v_isSharedCheck_4964_: u8 = 0;
    let mut v_cases_4965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_4966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_4968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_4969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4972_: u8 = 0;
    let mut v___x_4973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4978_: u8 = 0;
    let mut v___x_4979_: u8 = 0;
    let mut v___y_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: usize = 0;
    let mut v___x_4987_: usize = 0;
    let mut v___x_4988_: u8 = 0;
    let mut v___x_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4991_: u8 = 0;
    let mut v___x_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4998_: u8 = 0;
    let mut v_unused_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5000_: u8 = 0;
    let mut v_a_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5004_: u8 = 0;
    let mut v___x_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5008_: u8 = 0;
    let mut v_isSharedCheck_5009_: u8 = 0;
    let mut v_k_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: u8 = 0;
    let mut v___x_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_code_4910_) {
                0 => {
                    v_decl_4930_ = leanh::lean_ctor_get(v_code_4910_, 0);
                    v_value_4931_ = leanh::lean_ctor_get(v_decl_4930_, 3);
                    if leanh::lean_obj_tag(v_value_4931_) == 11 {
                        leanh::lean_inc_ref(v_decl_4930_);
                        v_k_4932_ = leanh::lean_ctor_get(v_code_4910_, 1);
                        leanh::lean_inc_ref(v_k_4932_);
                        leanh::lean_dec_ref_known(v_code_4910_, 2);
                        v_n_4933_ = leanh::lean_ctor_get(v_value_4931_, 0);
                        leanh::lean_inc(v_n_4933_);
                        v_var_4934_ = leanh::lean_ctor_get(v_value_4931_, 1);
                        leanh::lean_inc(v_var_4934_);
                        v___x_4935_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(v_currentRetType_4912_, v_ds_4911_, v_decl_4930_, v_n_4933_, v_var_4934_, v_k_4932_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_);
                        return v___x_4935_;
                    } else {
                        v_k_4936_ = leanh::lean_ctor_get(v_code_4910_, 1);
                        leanh::lean_inc_ref(v_k_4936_);
                        v_code_4919_ = v_code_4910_;
                        v_ds_4920_ = v_ds_4911_;
                        v_k_4921_ = v_k_4936_;
                        v___y_4922_ = v_a_4913_;
                        v___y_4923_ = v_a_4914_;
                        v___y_4924_ = v_a_4915_;
                        v___y_4925_ = v_a_4916_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_decl_4937_ = leanh::lean_ctor_get(v_code_4910_, 0);
                    leanh::lean_inc_ref(v_decl_4937_);
                    v_k_4938_ = leanh::lean_ctor_get(v_code_4910_, 1);
                    leanh::lean_inc_ref(v_k_4938_);
                    leanh::lean_dec_ref_known(v_code_4910_, 2);
                    v_params_4939_ = leanh::lean_ctor_get(v_decl_4937_, 2);
                    leanh::lean_inc_ref(v_params_4939_);
                    v_type_4940_ = leanh::lean_ctor_get(v_decl_4937_, 3);
                    leanh::lean_inc_ref_n(v_type_4940_, 2);
                    v_value_4941_ = leanh::lean_ctor_get(v_decl_4937_, 4);
                    v___x_4942_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0;
                    leanh::lean_inc_ref(v_value_4941_);
                    v___x_4943_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_value_4941_, v___x_4942_, v_type_4940_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_);
                    if leanh::lean_obj_tag(v___x_4943_) == 0 {
                        v_a_4944_ = leanh::lean_ctor_get(v___x_4943_, 0);
                        v_isSharedCheck_4964_ =
                            (!leanh::lean_is_exclusive(v___x_4943_)) as u8;
                        if v_isSharedCheck_4964_ == 0 {
                            v___x_4946_ = v___x_4943_;
                            v_isShared_4947_ = v_isSharedCheck_4964_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4944_);
                            leanh::lean_dec(v___x_4943_);
                            v___x_4946_ = leanh::lean_box(0);
                            v_isShared_4947_ = v_isSharedCheck_4964_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_type_4940_);
                        leanh::lean_dec_ref(v_params_4939_);
                        leanh::lean_dec_ref(v_k_4938_);
                        leanh::lean_dec_ref(v_decl_4937_);
                        leanh::lean_dec_ref(v_currentRetType_4912_);
                        leanh::lean_dec_ref(v_ds_4911_);
                        return v___x_4943_;
                    }
                }
                4 => {
                    leanh::lean_dec_ref(v_currentRetType_4912_);
                    v_cases_4965_ = leanh::lean_ctor_get(v_code_4910_, 0);
                    leanh::lean_inc_ref(v_cases_4965_);
                    v_typeName_4966_ = leanh::lean_ctor_get(v_cases_4965_, 0);
                    v_resultType_4967_ = leanh::lean_ctor_get(v_cases_4965_, 1);
                    v_discr_4968_ = leanh::lean_ctor_get(v_cases_4965_, 2);
                    v_alts_4969_ = leanh::lean_ctor_get(v_cases_4965_, 3);
                    v_isSharedCheck_5009_ = (!leanh::lean_is_exclusive(v_cases_4965_)) as u8;
                    if v_isSharedCheck_5009_ == 0 {
                        v___x_4971_ = v_cases_4965_;
                        v_isShared_4972_ = v_isSharedCheck_5009_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_alts_4969_);
                        leanh::lean_inc(v_discr_4968_);
                        leanh::lean_inc(v_resultType_4967_);
                        leanh::lean_inc(v_typeName_4966_);
                        leanh::lean_dec(v_cases_4965_);
                        v___x_4971_ = leanh::lean_box(0);
                        v_isShared_4972_ = v_isSharedCheck_5009_;
                        state = 6;
                        continue;
                    }
                }
                7 => {
                    v_k_5010_ = leanh::lean_ctor_get(v_code_4910_, 3);
                    leanh::lean_inc_ref(v_k_5010_);
                    v_code_4919_ = v_code_4910_;
                    v_ds_4920_ = v_ds_4911_;
                    v_k_4921_ = v_k_5010_;
                    v___y_4922_ = v_a_4913_;
                    v___y_4923_ = v_a_4914_;
                    v___y_4924_ = v_a_4915_;
                    v___y_4925_ = v_a_4916_;
                    state = 1;
                    continue;
                }
                8 => {
                    v_k_5011_ = leanh::lean_ctor_get(v_code_4910_, 3);
                    leanh::lean_inc_ref(v_k_5011_);
                    v_code_4919_ = v_code_4910_;
                    v_ds_4920_ = v_ds_4911_;
                    v_k_4921_ = v_k_5011_;
                    v___y_4922_ = v_a_4913_;
                    v___y_4923_ = v_a_4914_;
                    v___y_4924_ = v_a_4915_;
                    v___y_4925_ = v_a_4916_;
                    state = 1;
                    continue;
                }
                9 => {
                    v_k_5012_ = leanh::lean_ctor_get(v_code_4910_, 5);
                    leanh::lean_inc_ref(v_k_5012_);
                    v_code_4919_ = v_code_4910_;
                    v_ds_4920_ = v_ds_4911_;
                    v_k_4921_ = v_k_5012_;
                    v___y_4922_ = v_a_4913_;
                    v___y_4923_ = v_a_4914_;
                    v___y_4924_ = v_a_4915_;
                    v___y_4925_ = v_a_4916_;
                    state = 1;
                    continue;
                }
                10 => {
                    v_k_5013_ = leanh::lean_ctor_get(v_code_4910_, 2);
                    leanh::lean_inc_ref(v_k_5013_);
                    v_code_4919_ = v_code_4910_;
                    v_ds_4920_ = v_ds_4911_;
                    v_k_4921_ = v_k_5013_;
                    v___y_4922_ = v_a_4913_;
                    v___y_4923_ = v_a_4914_;
                    v___y_4924_ = v_a_4915_;
                    v___y_4925_ = v_a_4916_;
                    state = 1;
                    continue;
                }
                11 => {
                    v_k_5014_ = leanh::lean_ctor_get(v_code_4910_, 2);
                    leanh::lean_inc_ref(v_k_5014_);
                    v_code_4919_ = v_code_4910_;
                    v_ds_4920_ = v_ds_4911_;
                    v_k_4921_ = v_k_5014_;
                    v___y_4922_ = v_a_4913_;
                    v___y_4923_ = v_a_4914_;
                    v___y_4924_ = v_a_4915_;
                    v___y_4925_ = v_a_4916_;
                    state = 1;
                    continue;
                }
                12 => {
                    v_k_5015_ = leanh::lean_ctor_get(v_code_4910_, 3);
                    leanh::lean_inc_ref(v_k_5015_);
                    v_code_4919_ = v_code_4910_;
                    v_ds_4920_ = v_ds_4911_;
                    v_k_4921_ = v_k_5015_;
                    v___y_4922_ = v_a_4913_;
                    v___y_4923_ = v_a_4914_;
                    v___y_4924_ = v_a_4915_;
                    v___y_4925_ = v_a_4916_;
                    state = 1;
                    continue;
                }
                13 => {
                    v_k_5016_ = leanh::lean_ctor_get(v_code_4910_, 1);
                    leanh::lean_inc_ref(v_k_5016_);
                    v_code_4919_ = v_code_4910_;
                    v_ds_4920_ = v_ds_4911_;
                    v_k_4921_ = v_k_5016_;
                    v___y_4922_ = v_a_4913_;
                    v___y_4923_ = v_a_4914_;
                    v___y_4924_ = v_a_4915_;
                    v___y_4925_ = v_a_4916_;
                    state = 1;
                    continue;
                }
                _ => {
                    leanh::lean_dec_ref(v_currentRetType_4912_);
                    v___x_5017_ = 1;
                    v___x_5018_ =
                        l_Lean_Compiler_LCNF_attachCodeDecls(v___x_5017_, v_ds_4911_, v_code_4910_);
                    leanh::lean_dec_ref(v_ds_4911_);
                    v___x_5019_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5019_, 0, v___x_5018_);
                    return v___x_5019_;
                }
            },
            1 => {
                v___x_4926_ = 1;
                v_d_4927_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_4926_, v_code_4919_);
                leanh::lean_dec_ref(v_code_4919_);
                v___x_4928_ = lean_array_push(v_ds_4920_, v_d_4927_);
                v_code_4910_ = v_k_4921_;
                v_ds_4911_ = v___x_4928_;
                v_a_4913_ = v___y_4922_;
                v_a_4914_ = v___y_4923_;
                v_a_4915_ = v___y_4924_;
                v_a_4916_ = v___y_4925_;
                state = 0;
                continue;
            }
            2 => {
                v___x_4948_ = 1;
                v___x_4949_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_4948_, v_decl_4937_, v_type_4940_, v_params_4939_, v_a_4944_, v_a_4914_);
                if leanh::lean_obj_tag(v___x_4949_) == 0 {
                    v_a_4950_ = leanh::lean_ctor_get(v___x_4949_, 0);
                    leanh::lean_inc(v_a_4950_);
                    leanh::lean_dec_ref_known(v___x_4949_, 1);
                    if v_isShared_4947_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4946_, 2);
                        leanh::lean_ctor_set(v___x_4946_, 0, v_a_4950_);
                        v___x_4952_ = v___x_4946_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4955_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4955_, 0, v_a_4950_);
                        v___x_4952_ = v_reuseFailAlloc_4955_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4946_);
                    leanh::lean_dec_ref(v_k_4938_);
                    leanh::lean_dec_ref(v_currentRetType_4912_);
                    leanh::lean_dec_ref(v_ds_4911_);
                    v_a_4956_ = leanh::lean_ctor_get(v___x_4949_, 0);
                    v_isSharedCheck_4963_ = (!leanh::lean_is_exclusive(v___x_4949_)) as u8;
                    if v_isSharedCheck_4963_ == 0 {
                        v___x_4958_ = v___x_4949_;
                        v_isShared_4959_ = v_isSharedCheck_4963_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4956_);
                        leanh::lean_dec(v___x_4949_);
                        v___x_4958_ = leanh::lean_box(0);
                        v_isShared_4959_ = v_isSharedCheck_4963_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4953_ = lean_array_push(v_ds_4911_, v___x_4952_);
                v_code_4910_ = v_k_4938_;
                v_ds_4911_ = v___x_4953_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_4959_ == 0 {
                    v___x_4961_ = v___x_4958_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4962_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4962_, 0, v_a_4956_);
                    v___x_4961_ = v_reuseFailAlloc_4962_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4961_;
            }
            6 => {
                v___x_4973_ = leanh::lean_unsigned_to_nat(0);
                leanh::lean_inc_ref(v_alts_4969_);
                leanh::lean_inc_ref(v_resultType_4967_);
                v___x_4974_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(v_resultType_4967_, v___x_4973_, v_alts_4969_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_);
                if leanh::lean_obj_tag(v___x_4974_) == 0 {
                    v_a_4975_ = leanh::lean_ctor_get(v___x_4974_, 0);
                    v_isSharedCheck_5000_ = (!leanh::lean_is_exclusive(v___x_4974_)) as u8;
                    if v_isSharedCheck_5000_ == 0 {
                        v___x_4977_ = v___x_4974_;
                        v_isShared_4978_ = v_isSharedCheck_5000_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4975_);
                        leanh::lean_dec(v___x_4974_);
                        v___x_4977_ = leanh::lean_box(0);
                        v_isShared_4978_ = v_isSharedCheck_5000_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4971_);
                    leanh::lean_dec_ref(v_alts_4969_);
                    leanh::lean_dec(v_discr_4968_);
                    leanh::lean_dec_ref(v_resultType_4967_);
                    leanh::lean_dec(v_typeName_4966_);
                    leanh::lean_dec_ref_known(v_code_4910_, 1);
                    leanh::lean_dec_ref(v_ds_4911_);
                    v_a_5001_ = leanh::lean_ctor_get(v___x_4974_, 0);
                    v_isSharedCheck_5008_ = (!leanh::lean_is_exclusive(v___x_4974_)) as u8;
                    if v_isSharedCheck_5008_ == 0 {
                        v___x_5003_ = v___x_4974_;
                        v_isShared_5004_ = v_isSharedCheck_5008_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5001_);
                        leanh::lean_dec(v___x_4974_);
                        v___x_5003_ = leanh::lean_box(0);
                        v_isShared_5004_ = v_isSharedCheck_5008_;
                        state = 13;
                        continue;
                    }
                }
            }
            7 => {
                v___x_4979_ = 1;
                v___x_4986_ = lean_ptr_addr(v_alts_4969_);
                leanh::lean_dec_ref(v_alts_4969_);
                v___x_4987_ = lean_ptr_addr(v_a_4975_);
                v___x_4988_ = lean_usize_dec_eq(v___x_4986_, v___x_4987_);
                if v___x_4988_ == 0 {
                    v_isSharedCheck_4998_ = (!leanh::lean_is_exclusive(v_code_4910_)) as u8;
                    if v_isSharedCheck_4998_ == 0 {
                        v_unused_4999_ = leanh::lean_ctor_get(v_code_4910_, 0);
                        leanh::lean_dec(v_unused_4999_);
                        v___x_4990_ = v_code_4910_;
                        v_isShared_4991_ = v_isSharedCheck_4998_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_dec(v_code_4910_);
                        v___x_4990_ = leanh::lean_box(0);
                        v_isShared_4991_ = v_isSharedCheck_4998_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4975_);
                    leanh::lean_del_object(v___x_4971_);
                    leanh::lean_dec(v_discr_4968_);
                    leanh::lean_dec_ref(v_resultType_4967_);
                    leanh::lean_dec(v_typeName_4966_);
                    v___y_4981_ = v_code_4910_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4982_ =
                    l_Lean_Compiler_LCNF_attachCodeDecls(v___x_4979_, v_ds_4911_, v___y_4981_);
                leanh::lean_dec_ref(v_ds_4911_);
                if v_isShared_4978_ == 0 {
                    leanh::lean_ctor_set(v___x_4977_, 0, v___x_4982_);
                    v___x_4984_ = v___x_4977_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4985_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4985_, 0, v___x_4982_);
                    v___x_4984_ = v_reuseFailAlloc_4985_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4984_;
            }
            10 => {
                if v_isShared_4972_ == 0 {
                    leanh::lean_ctor_set(v___x_4971_, 3, v_a_4975_);
                    v___x_4993_ = v___x_4971_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4997_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4997_, 0, v_typeName_4966_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4997_, 1, v_resultType_4967_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4997_, 2, v_discr_4968_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4997_, 3, v_a_4975_);
                    v___x_4993_ = v_reuseFailAlloc_4997_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_4991_ == 0 {
                    leanh::lean_ctor_set(v___x_4990_, 0, v___x_4993_);
                    v___x_4995_ = v___x_4990_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4996_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4996_, 0, v___x_4993_);
                    v___x_4995_ = v_reuseFailAlloc_4996_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___y_4981_ = v___x_4995_;
                state = 8;
                continue;
            }
            13 => {
                if v_isShared_5004_ == 0 {
                    v___x_5006_ = v___x_5003_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5007_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5007_, 0, v_a_5001_);
                    v___x_5006_ = v_reuseFailAlloc_5007_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5006_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0(
    mut v_resultType_5020_: *mut leanh::LeanObject,
    mut v_x_5021_: *mut leanh::LeanObject,
    mut v___y_5022_: *mut leanh::LeanObject,
    mut v___y_5023_: *mut leanh::LeanObject,
    mut v___y_5024_: *mut leanh::LeanObject,
    mut v___y_5025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5027_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0;
    v___x_5028_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(
            v_x_5021_,
            v___x_5027_,
            v_resultType_5020_,
            v___y_5022_,
            v___y_5023_,
            v___y_5024_,
            v___y_5025_,
        );
    return v___x_5028_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___boxed(
    mut v_resultType_5029_: *mut leanh::LeanObject,
    mut v_i_5030_: *mut leanh::LeanObject,
    mut v_as_5031_: *mut leanh::LeanObject,
    mut v___y_5032_: *mut leanh::LeanObject,
    mut v___y_5033_: *mut leanh::LeanObject,
    mut v___y_5034_: *mut leanh::LeanObject,
    mut v___y_5035_: *mut leanh::LeanObject,
    mut v___y_5036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5037_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(v_resultType_5029_, v_i_5030_, v_as_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_);
    leanh::lean_dec(v___y_5035_);
    leanh::lean_dec_ref(v___y_5034_);
    leanh::lean_dec(v___y_5033_);
    leanh::lean_dec_ref(v___y_5032_);
    return v_res_5037_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse___boxed(
    mut v_code_5038_: *mut leanh::LeanObject,
    mut v_ds_5039_: *mut leanh::LeanObject,
    mut v_currentRetType_5040_: *mut leanh::LeanObject,
    mut v_a_5041_: *mut leanh::LeanObject,
    mut v_a_5042_: *mut leanh::LeanObject,
    mut v_a_5043_: *mut leanh::LeanObject,
    mut v_a_5044_: *mut leanh::LeanObject,
    mut v_a_5045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5046_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(
            v_code_5038_,
            v_ds_5039_,
            v_currentRetType_5040_,
            v_a_5041_,
            v_a_5042_,
            v_a_5043_,
            v_a_5044_,
        );
    leanh::lean_dec(v_a_5044_);
    leanh::lean_dec_ref(v_a_5043_);
    leanh::lean_dec(v_a_5042_);
    leanh::lean_dec_ref(v_a_5041_);
    return v_res_5046_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___boxed(
    mut v_currentRetType_5047_: *mut leanh::LeanObject,
    mut v_ds_5048_: *mut leanh::LeanObject,
    mut v_decl_5049_: *mut leanh::LeanObject,
    mut v_nFields_5050_: *mut leanh::LeanObject,
    mut v_origAllocId_5051_: *mut leanh::LeanObject,
    mut v_k_5052_: *mut leanh::LeanObject,
    mut v_a_5053_: *mut leanh::LeanObject,
    mut v_a_5054_: *mut leanh::LeanObject,
    mut v_a_5055_: *mut leanh::LeanObject,
    mut v_a_5056_: *mut leanh::LeanObject,
    mut v_a_5057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5058_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(v_currentRetType_5047_, v_ds_5048_, v_decl_5049_, v_nFields_5050_, v_origAllocId_5051_, v_k_5052_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_);
    leanh::lean_dec(v_a_5056_);
    leanh::lean_dec_ref(v_a_5055_);
    leanh::lean_dec(v_a_5054_);
    leanh::lean_dec_ref(v_a_5053_);
    return v_res_5058_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(
    mut v_f_5059_: *mut leanh::LeanObject,
    mut v_v_5060_: *mut leanh::LeanObject,
    mut v___y_5061_: *mut leanh::LeanObject,
    mut v___y_5062_: *mut leanh::LeanObject,
    mut v___y_5063_: *mut leanh::LeanObject,
    mut v___y_5064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_code_5066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5069_: u8 = 0;
    let mut v___x_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5074_: u8 = 0;
    let mut v___x_5076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5081_: u8 = 0;
    let mut v_a_5082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5085_: u8 = 0;
    let mut v___x_5087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5089_: u8 = 0;
    let mut v_isSharedCheck_5090_: u8 = 0;
    let mut v___x_5091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_v_5060_) == 0 {
                    v_code_5066_ = leanh::lean_ctor_get(v_v_5060_, 0);
                    v_isSharedCheck_5090_ = (!leanh::lean_is_exclusive(v_v_5060_)) as u8;
                    if v_isSharedCheck_5090_ == 0 {
                        v___x_5068_ = v_v_5060_;
                        v_isShared_5069_ = v_isSharedCheck_5090_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_code_5066_);
                        leanh::lean_dec(v_v_5060_);
                        v___x_5068_ = leanh::lean_box(0);
                        v_isShared_5069_ = v_isSharedCheck_5090_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_f_5059_);
                    v___x_5091_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5091_, 0, v_v_5060_);
                    return v___x_5091_;
                }
            }
            1 => {
                leanh::lean_inc(v___y_5064_);
                leanh::lean_inc_ref(v___y_5063_);
                leanh::lean_inc(v___y_5062_);
                leanh::lean_inc_ref(v___y_5061_);
                v___x_5070_ = leanh::lean_apply_6(
                    v_f_5059_,
                    v_code_5066_,
                    v___y_5061_,
                    v___y_5062_,
                    v___y_5063_,
                    v___y_5064_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_5070_) == 0 {
                    v_a_5071_ = leanh::lean_ctor_get(v___x_5070_, 0);
                    v_isSharedCheck_5081_ = (!leanh::lean_is_exclusive(v___x_5070_)) as u8;
                    if v_isSharedCheck_5081_ == 0 {
                        v___x_5073_ = v___x_5070_;
                        v_isShared_5074_ = v_isSharedCheck_5081_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5071_);
                        leanh::lean_dec(v___x_5070_);
                        v___x_5073_ = leanh::lean_box(0);
                        v_isShared_5074_ = v_isSharedCheck_5081_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5068_);
                    v_a_5082_ = leanh::lean_ctor_get(v___x_5070_, 0);
                    v_isSharedCheck_5089_ = (!leanh::lean_is_exclusive(v___x_5070_)) as u8;
                    if v_isSharedCheck_5089_ == 0 {
                        v___x_5084_ = v___x_5070_;
                        v_isShared_5085_ = v_isSharedCheck_5089_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5082_);
                        leanh::lean_dec(v___x_5070_);
                        v___x_5084_ = leanh::lean_box(0);
                        v_isShared_5085_ = v_isSharedCheck_5089_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5069_ == 0 {
                    leanh::lean_ctor_set(v___x_5068_, 0, v_a_5071_);
                    v___x_5076_ = v___x_5068_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5080_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5080_, 0, v_a_5071_);
                    v___x_5076_ = v_reuseFailAlloc_5080_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5074_ == 0 {
                    leanh::lean_ctor_set(v___x_5073_, 0, v___x_5076_);
                    v___x_5078_ = v___x_5073_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5079_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5079_, 0, v___x_5076_);
                    v___x_5078_ = v_reuseFailAlloc_5079_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5078_;
            }
            5 => {
                if v_isShared_5085_ == 0 {
                    v___x_5087_ = v___x_5084_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5088_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5088_, 0, v_a_5082_);
                    v___x_5087_ = v_reuseFailAlloc_5088_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5087_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg___boxed(
    mut v_f_5092_: *mut leanh::LeanObject,
    mut v_v_5093_: *mut leanh::LeanObject,
    mut v___y_5094_: *mut leanh::LeanObject,
    mut v___y_5095_: *mut leanh::LeanObject,
    mut v___y_5096_: *mut leanh::LeanObject,
    mut v___y_5097_: *mut leanh::LeanObject,
    mut v___y_5098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5099_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v_f_5092_, v_v_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_);
    leanh::lean_dec(v___y_5097_);
    leanh::lean_dec_ref(v___y_5096_);
    leanh::lean_dec(v___y_5095_);
    leanh::lean_dec_ref(v___y_5094_);
    return v_res_5099_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0(
    mut v_pu_5100_: u8,
    mut v_f_5101_: *mut leanh::LeanObject,
    mut v_v_5102_: *mut leanh::LeanObject,
    mut v___y_5103_: *mut leanh::LeanObject,
    mut v___y_5104_: *mut leanh::LeanObject,
    mut v___y_5105_: *mut leanh::LeanObject,
    mut v___y_5106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5108_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v_f_5101_, v_v_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_);
    return v___x_5108_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___boxed(
    mut v_pu_5109_: *mut leanh::LeanObject,
    mut v_f_5110_: *mut leanh::LeanObject,
    mut v_v_5111_: *mut leanh::LeanObject,
    mut v___y_5112_: *mut leanh::LeanObject,
    mut v___y_5113_: *mut leanh::LeanObject,
    mut v___y_5114_: *mut leanh::LeanObject,
    mut v___y_5115_: *mut leanh::LeanObject,
    mut v___y_5116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_5117_: u8 = 0;
    let mut v_res_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5117_ = (leanh::lean_unbox(v_pu_5109_) as u8);
    v_res_5118_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0(v_pu_boxed_5117_, v_f_5110_, v_v_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_);
    leanh::lean_dec(v___y_5115_);
    leanh::lean_dec_ref(v___y_5114_);
    leanh::lean_dec(v___y_5113_);
    leanh::lean_dec_ref(v___y_5112_);
    return v_res_5118_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0(
    mut v_toSignature_5119_: *mut leanh::LeanObject,
    mut v_x_5120_: *mut leanh::LeanObject,
    mut v___y_5121_: *mut leanh::LeanObject,
    mut v___y_5122_: *mut leanh::LeanObject,
    mut v___y_5123_: *mut leanh::LeanObject,
    mut v___y_5124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_type_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_type_5126_ = leanh::lean_ctor_get(v_toSignature_5119_, 2);
    leanh::lean_inc_ref(v_type_5126_);
    leanh::lean_dec_ref(v_toSignature_5119_);
    v___x_5127_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0;
    v___x_5128_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(
            v_x_5120_,
            v___x_5127_,
            v_type_5126_,
            v___y_5121_,
            v___y_5122_,
            v___y_5123_,
            v___y_5124_,
        );
    return v___x_5128_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0___boxed(
    mut v_toSignature_5129_: *mut leanh::LeanObject,
    mut v_x_5130_: *mut leanh::LeanObject,
    mut v___y_5131_: *mut leanh::LeanObject,
    mut v___y_5132_: *mut leanh::LeanObject,
    mut v___y_5133_: *mut leanh::LeanObject,
    mut v___y_5134_: *mut leanh::LeanObject,
    mut v___y_5135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5136_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0(v_toSignature_5129_, v_x_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_);
    leanh::lean_dec(v___y_5134_);
    leanh::lean_dec_ref(v___y_5133_);
    leanh::lean_dec(v___y_5132_);
    leanh::lean_dec_ref(v___y_5131_);
    return v_res_5136_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse(
    mut v_decl_5137_: *mut leanh::LeanObject,
    mut v_a_5138_: *mut leanh::LeanObject,
    mut v_a_5139_: *mut leanh::LeanObject,
    mut v_a_5140_: *mut leanh::LeanObject,
    mut v_a_5141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5147_: u8 = 0;
    let mut v_resetReuse_5148_: u8 = 0;
    let mut v___x_5150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursive_5154_: u8 = 0;
    let mut v_inlineAttr_x3f_5155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5158_: u8 = 0;
    let mut v___f_5159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5164_: u8 = 0;
    let mut v___x_5166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5171_: u8 = 0;
    let mut v_a_5172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5175_: u8 = 0;
    let mut v___x_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5179_: u8 = 0;
    let mut v_isSharedCheck_5180_: u8 = 0;
    let mut v_isSharedCheck_5181_: u8 = 0;
    let mut v_a_5182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5185_: u8 = 0;
    let mut v___x_5187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5189_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5143_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_5138_);
                if leanh::lean_obj_tag(v___x_5143_) == 0 {
                    v_a_5144_ = leanh::lean_ctor_get(v___x_5143_, 0);
                    v_isSharedCheck_5181_ = (!leanh::lean_is_exclusive(v___x_5143_)) as u8;
                    if v_isSharedCheck_5181_ == 0 {
                        v___x_5146_ = v___x_5143_;
                        v_isShared_5147_ = v_isSharedCheck_5181_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5144_);
                        leanh::lean_dec(v___x_5143_);
                        v___x_5146_ = leanh::lean_box(0);
                        v_isShared_5147_ = v_isSharedCheck_5181_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_decl_5137_);
                    v_a_5182_ = leanh::lean_ctor_get(v___x_5143_, 0);
                    v_isSharedCheck_5189_ = (!leanh::lean_is_exclusive(v___x_5143_)) as u8;
                    if v_isSharedCheck_5189_ == 0 {
                        v___x_5184_ = v___x_5143_;
                        v_isShared_5185_ = v_isSharedCheck_5189_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5182_);
                        leanh::lean_dec(v___x_5143_);
                        v___x_5184_ = leanh::lean_box(0);
                        v_isShared_5185_ = v_isSharedCheck_5189_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_resetReuse_5148_ = leanh::lean_ctor_get_uint8(
                    v_a_5144_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 2) as u32,
                );
                leanh::lean_dec(v_a_5144_);
                if v_resetReuse_5148_ == 0 {
                    if v_isShared_5147_ == 0 {
                        leanh::lean_ctor_set(v___x_5146_, 0, v_decl_5137_);
                        v___x_5150_ = v___x_5146_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5151_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5151_, 0, v_decl_5137_);
                        v___x_5150_ = v_reuseFailAlloc_5151_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5146_);
                    v_toSignature_5152_ = leanh::lean_ctor_get(v_decl_5137_, 0);
                    v_value_5153_ = leanh::lean_ctor_get(v_decl_5137_, 1);
                    v_recursive_5154_ = leanh::lean_ctor_get_uint8(
                        v_decl_5137_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    v_inlineAttr_x3f_5155_ = leanh::lean_ctor_get(v_decl_5137_, 2);
                    v_isSharedCheck_5180_ = (!leanh::lean_is_exclusive(v_decl_5137_)) as u8;
                    if v_isSharedCheck_5180_ == 0 {
                        v___x_5157_ = v_decl_5137_;
                        v_isShared_5158_ = v_isSharedCheck_5180_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_inlineAttr_x3f_5155_);
                        leanh::lean_inc(v_value_5153_);
                        leanh::lean_inc(v_toSignature_5152_);
                        leanh::lean_dec(v_decl_5137_);
                        v___x_5157_ = leanh::lean_box(0);
                        v_isShared_5158_ = v_isSharedCheck_5180_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5150_;
            }
            3 => {
                leanh::lean_inc_ref(v_toSignature_5152_);
                v___f_5159_ = leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                leanh::lean_closure_set(v___f_5159_, 0, v_toSignature_5152_);
                v___x_5160_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v___f_5159_, v_value_5153_, v_a_5138_, v_a_5139_, v_a_5140_, v_a_5141_);
                if leanh::lean_obj_tag(v___x_5160_) == 0 {
                    v_a_5161_ = leanh::lean_ctor_get(v___x_5160_, 0);
                    v_isSharedCheck_5171_ = (!leanh::lean_is_exclusive(v___x_5160_)) as u8;
                    if v_isSharedCheck_5171_ == 0 {
                        v___x_5163_ = v___x_5160_;
                        v_isShared_5164_ = v_isSharedCheck_5171_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5161_);
                        leanh::lean_dec(v___x_5160_);
                        v___x_5163_ = leanh::lean_box(0);
                        v_isShared_5164_ = v_isSharedCheck_5171_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5157_);
                    leanh::lean_dec(v_inlineAttr_x3f_5155_);
                    leanh::lean_dec_ref(v_toSignature_5152_);
                    v_a_5172_ = leanh::lean_ctor_get(v___x_5160_, 0);
                    v_isSharedCheck_5179_ = (!leanh::lean_is_exclusive(v___x_5160_)) as u8;
                    if v_isSharedCheck_5179_ == 0 {
                        v___x_5174_ = v___x_5160_;
                        v_isShared_5175_ = v_isSharedCheck_5179_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5172_);
                        leanh::lean_dec(v___x_5160_);
                        v___x_5174_ = leanh::lean_box(0);
                        v_isShared_5175_ = v_isSharedCheck_5179_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_5158_ == 0 {
                    leanh::lean_ctor_set(v___x_5157_, 1, v_a_5161_);
                    v___x_5166_ = v___x_5157_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5170_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 0, v_toSignature_5152_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 1, v_a_5161_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 2, v_inlineAttr_x3f_5155_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5170_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_recursive_5154_,
                    );
                    v___x_5166_ = v_reuseFailAlloc_5170_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5164_ == 0 {
                    leanh::lean_ctor_set(v___x_5163_, 0, v___x_5166_);
                    v___x_5168_ = v___x_5163_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5169_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5169_, 0, v___x_5166_);
                    v___x_5168_ = v_reuseFailAlloc_5169_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5168_;
            }
            7 => {
                if v_isShared_5175_ == 0 {
                    v___x_5177_ = v___x_5174_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5178_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5178_, 0, v_a_5172_);
                    v___x_5177_ = v_reuseFailAlloc_5178_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5177_;
            }
            9 => {
                if v_isShared_5185_ == 0 {
                    v___x_5187_ = v___x_5184_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5188_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5188_, 0, v_a_5182_);
                    v___x_5187_ = v_reuseFailAlloc_5188_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5187_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___boxed(
    mut v_decl_5190_: *mut leanh::LeanObject,
    mut v_a_5191_: *mut leanh::LeanObject,
    mut v_a_5192_: *mut leanh::LeanObject,
    mut v_a_5193_: *mut leanh::LeanObject,
    mut v_a_5194_: *mut leanh::LeanObject,
    mut v_a_5195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5196_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse(
            v_decl_5190_,
            v_a_5191_,
            v_a_5192_,
            v_a_5193_,
            v_a_5194_,
        );
    leanh::lean_dec(v_a_5194_);
    leanh::lean_dec_ref(v_a_5193_);
    leanh::lean_dec(v_a_5192_);
    leanh::lean_dec_ref(v_a_5191_);
    return v_res_5196_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_expandResetReuse___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: u8 = 0;
    let mut v___x_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5201_ = leanh::lean_unsigned_to_nat(0);
    v___x_5202_ = l_Lean_Compiler_LCNF_expandResetReuse___closed__2;
    v___x_5203_ = 2;
    v___x_5204_ = l_Lean_Compiler_LCNF_expandResetReuse___closed__1;
    v___x_5205_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(
        v___x_5204_,
        v___x_5203_,
        v___x_5202_,
        v___x_5201_,
    );
    return v___x_5205_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_expandResetReuse() -> *mut leanh::LeanObject {
    let mut v___x_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5206_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_expandResetReuse___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_expandResetReuse___closed__3_once),
        _init_l_Lean_Compiler_LCNF_expandResetReuse___closed__3,
    );
    return v___x_5206_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5262_ = leanh::lean_unsigned_to_nat(2743268278);
    v___x_5263_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_;
    v___x_5264_ = l_Lean_Name_num___override(v___x_5263_, v___x_5262_);
    return v___x_5264_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5266_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_;
    v___x_5267_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
    v___x_5268_ = l_Lean_Name_str___override(v___x_5267_, v___x_5266_);
    return v___x_5268_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_5270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5270_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_;
    v___x_5271_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
    v___x_5272_ = l_Lean_Name_str___override(v___x_5271_, v___x_5270_);
    return v___x_5272_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_5273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5273_ = leanh::lean_unsigned_to_nat(2);
    v___x_5274_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
    v___x_5275_ = l_Lean_Name_num___override(v___x_5274_, v___x_5273_);
    return v___x_5275_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: u8 = 0;
    let mut v___x_5279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5277_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_;
    v___x_5278_ = 1;
    v___x_5279_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
    v___x_5280_ = l_Lean_registerTraceClass(v___x_5277_, v___x_5278_, v___x_5279_);
    return v___x_5280_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2____boxed(
    mut v_a_5281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5282_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_();
    return v_res_5282_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_ExpandResetReuse(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Compiler_LCNF_expandResetReuse = _init_l_Lean_Compiler_LCNF_expandResetReuse();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_expandResetReuse);
    res = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_ExpandResetReuse(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_ExpandResetReuse(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ExpandResetReuse(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_ExpandResetReuse(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_ExpandResetReuse(builtin);
}
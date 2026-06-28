// Lean compiler output
// Module: Lean.Compiler.LCNF.ExpandResetReuse
// Imports: Lean.Compiler.LCNF.PassManager Init.While
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::{
    l_Array_append___redArg, l_Array_instInhabited, l_Array_reverse___redArg,
};
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_pop, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::{lean_array_fset, lean_array_set};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_5,
    lean_apply_6, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2_value) as *mut LeanObject;
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1_value: LeanStringObject<36> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 69, 120, 112, 97, 110, 100, 82, 101, 115, 101, 116, 82, 101, 117, 115, 101, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__2_value: LeanStringObject<82> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 82, m_capacity: 82, m_length: 81, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 69, 120, 112, 97, 110, 100, 82, 101, 115, 101, 116, 82, 101, 117, 115, 101, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 101, 114, 97, 115, 101, 80, 114, 111, 106, 73, 110, 99, 70, 111, 114, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__3_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 110, 32, 62, 32, 48, 32, 45, 45, 32, 48, 32, 105, 110, 99, 115, 32, 115, 104, 111, 117, 108, 100, 32, 110, 111, 116, 32, 98, 101, 32, 104, 97, 112, 112, 101, 110, 105, 110, 103, 10, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__3_value) as *mut LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 111, 111, 108, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__1_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__1_value) as *mut LeanObject;
static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__0_value) as *mut LeanObject,12882480457794858234 as *mut LeanObject] };
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__1_value) as *mut LeanObject,15761733860085307253 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__3_value: LeanCtorObject<5> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__4_value) as *mut LeanObject;
static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__0_value) as *mut LeanObject,12882480457794858234 as *mut LeanObject] };
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__4_value) as *mut LeanObject,9255189395584251158 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__6_value: LeanCtorObject<5> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5_value) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__6_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__0_value: LeanStringObject<76> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 76, m_capacity: 76, m_length: 75, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 69, 120, 112, 97, 110, 100, 82, 101, 115, 101, 116, 82, 101, 117, 115, 101, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 114, 101, 109, 97, 112, 83, 101, 116, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__0_value: LeanStringObject<84> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 84, m_capacity: 84, m_length: 83, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 69, 120, 112, 97, 110, 100, 82, 101, 115, 101, 116, 82, 101, 117, 115, 101, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 112, 97, 114, 116, 105, 116, 105, 111, 110, 83, 101, 108, 102, 83, 101, 116, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___closed__0_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [117, 110, 117, 115, 101, 100, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__0_value) as *mut LeanObject,8495011437180164029 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 111, 98, 106, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__2_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__2_value) as *mut LeanObject,930430701391226905 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__3_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__0_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [114, 101, 117, 115, 101, 70, 97, 105, 108, 65, 108, 108, 111, 99, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__0_value) as *mut LeanObject,1965393245545708194 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__1_value) as *mut LeanObject;
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 117, 115, 101, 106, 112, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__0_value) as *mut LeanObject,16585790626105456024 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [85, 73, 110, 116, 56, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__2_value) as *mut LeanObject,15764114953608429200 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__6_value: LeanStringObject<84> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 84, m_capacity: 84, m_length: 83, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 110, 32, 61, 61, 32, 49, 32, 45, 45, 32, 110, 32, 109, 117, 115, 116, 32, 98, 101, 32, 111, 110, 101, 32, 115, 105, 110, 99, 101, 32, 96, 114, 101, 115, 101, 116, 84, 111, 107, 101, 110, 32, 58, 61, 32, 114, 101, 115, 101, 116, 32, 46, 46, 46, 96, 10, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5_value: LeanStringObject<83> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 83, m_capacity: 83, m_length: 82, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 69, 120, 112, 97, 110, 100, 82, 101, 115, 101, 116, 82, 101, 117, 115, 101, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 112, 114, 111, 99, 101, 115, 115, 82, 101, 115, 101, 116, 67, 111, 110, 116, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 115, 83, 104, 97, 114, 101, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__0_value) as *mut LeanObject,16304350630193599974 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 115, 101, 116, 106, 112, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__2_value) as *mut LeanObject,7530470289044155581 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__4_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [105, 115, 83, 104, 97, 114, 101, 100, 67, 104, 101, 99, 107, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__4_value) as *mut LeanObject,8080113652283748063 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__5_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_expandResetReuse___closed__0_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_expandResetReuse___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_expandResetReuse___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_expandResetReuse___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_expandResetReuse___closed__0_value)
                as *mut LeanObject,
            14075296980557281220 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_expandResetReuse___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_expandResetReuse___closed__1_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_expandResetReuse___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Compiler_LCNF_expandResetReuse___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_expandResetReuse___closed__2_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_expandResetReuse___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_expandResetReuse___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_expandResetReuse: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,2042452093243897853 as *mut LeanObject] };
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_expandResetReuse___closed__0_value) as *mut LeanObject,4700002501560739034 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,1501781890156459336 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,4203849195465939425 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [69, 120, 112, 97, 110, 100, 82, 101, 115, 101, 116, 82, 101, 117, 115, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,4716892160583994151 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,5381860422951367578 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,6136025083668818235 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,131487144209835133 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,15922225652527654984 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,10324035721225016549 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,14500088037220215128 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,6052734082724814545 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,7077821464577668063 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,16536633794523358290 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject,16492176252976513240 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    v___x_2642_ = l_instMonadEIO(lean_box(0));
    return v___x_2642_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    v___x_2645_ = l_Array_instInhabited(lean_box(0));
    return v___x_2645_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0(
    mut v_msg_2646_: *mut LeanObject,
    mut v___y_2647_: *mut LeanObject,
    mut v___y_2648_: *mut LeanObject,
    mut v___y_2649_: *mut LeanObject,
    mut v___y_2650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2657_: u8 = 0;
    let mut v_toFunctor_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2664_: u8 = 0;
    let mut v___f_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2915__overap_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2688_: u8 = 0;
    let mut v_unused_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2690_: u8 = 0;
    let mut v_unused_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2652_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0);
                v___x_2653_ = l_StateRefT_x27_instMonad___redArg(v___x_2652_);
                v_toApplicative_2654_ = lean_ctor_get(v___x_2653_, 0);
                v_isSharedCheck_2690_ = (!lean_is_exclusive(v___x_2653_)) as u8;
                if v_isSharedCheck_2690_ == 0 {
                    v_unused_2691_ = lean_ctor_get(v___x_2653_, 1);
                    lean_dec(v_unused_2691_);
                    v___x_2656_ = v___x_2653_;
                    v_isShared_2657_ = v_isSharedCheck_2690_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_2654_);
                    lean_dec(v___x_2653_);
                    v___x_2656_ = lean_box(0);
                    v_isShared_2657_ = v_isSharedCheck_2690_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2658_ = lean_ctor_get(v_toApplicative_2654_, 0);
                v_toSeq_2659_ = lean_ctor_get(v_toApplicative_2654_, 2);
                v_toSeqLeft_2660_ = lean_ctor_get(v_toApplicative_2654_, 3);
                v_toSeqRight_2661_ = lean_ctor_get(v_toApplicative_2654_, 4);
                v_isSharedCheck_2688_ = (!lean_is_exclusive(v_toApplicative_2654_)) as u8;
                if v_isSharedCheck_2688_ == 0 {
                    v_unused_2689_ = lean_ctor_get(v_toApplicative_2654_, 1);
                    lean_dec(v_unused_2689_);
                    v___x_2663_ = v_toApplicative_2654_;
                    v_isShared_2664_ = v_isSharedCheck_2688_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_2661_);
                    lean_inc(v_toSeqLeft_2660_);
                    lean_inc(v_toSeq_2659_);
                    lean_inc(v_toFunctor_2658_);
                    lean_dec(v_toApplicative_2654_);
                    v___x_2663_ = lean_box(0);
                    v_isShared_2664_ = v_isSharedCheck_2688_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2665_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1;
                v___f_2666_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2;
                lean_inc_ref(v_toFunctor_2658_);
                v___f_2667_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2667_, 0, v_toFunctor_2658_);
                v___f_2668_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2668_, 0, v_toFunctor_2658_);
                v___x_2669_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2669_, 0, v___f_2667_);
                lean_ctor_set(v___x_2669_, 1, v___f_2668_);
                v___f_2670_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2670_, 0, v_toSeqRight_2661_);
                v___f_2671_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2671_, 0, v_toSeqLeft_2660_);
                v___f_2672_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2672_, 0, v_toSeq_2659_);
                if v_isShared_2664_ == 0 {
                    lean_ctor_set(v___x_2663_, 4, v___f_2670_);
                    lean_ctor_set(v___x_2663_, 3, v___f_2671_);
                    lean_ctor_set(v___x_2663_, 2, v___f_2672_);
                    lean_ctor_set(v___x_2663_, 1, v___f_2665_);
                    lean_ctor_set(v___x_2663_, 0, v___x_2669_);
                    v___x_2674_ = v___x_2663_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2669_);
                    lean_ctor_set(v_reuseFailAlloc_2687_, 1, v___f_2665_);
                    lean_ctor_set(v_reuseFailAlloc_2687_, 2, v___f_2672_);
                    lean_ctor_set(v_reuseFailAlloc_2687_, 3, v___f_2671_);
                    lean_ctor_set(v_reuseFailAlloc_2687_, 4, v___f_2670_);
                    v___x_2674_ = v_reuseFailAlloc_2687_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2657_ == 0 {
                    lean_ctor_set(v___x_2656_, 1, v___f_2666_);
                    lean_ctor_set(v___x_2656_, 0, v___x_2674_);
                    v___x_2676_ = v___x_2656_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2674_);
                    lean_ctor_set(v_reuseFailAlloc_2686_, 1, v___f_2666_);
                    v___x_2676_ = v_reuseFailAlloc_2686_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2677_ = l_StateRefT_x27_instMonad___redArg(v___x_2676_);
                v___x_2678_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3);
                v___x_2679_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2679_, 0, v___x_2678_);
                lean_ctor_set(v___x_2679_, 1, v___x_2678_);
                v___x_2680_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2680_, 0, v___x_2678_);
                lean_ctor_set(v___x_2680_, 1, v___x_2679_);
                v___x_2681_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2681_, 0, v___x_2680_);
                v___x_2682_ = l_instInhabitedOfMonad___redArg(v___x_2677_, v___x_2681_);
                v___f_2683_ = lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_2683_, 0, v___x_2682_);
                v___x_2915__overap_2684_ = lean_panic_fn_borrowed(v___f_2683_, v_msg_2646_);
                lean_dec_ref(v___f_2683_);
                lean_inc(v___y_2650_);
                lean_inc_ref(v___y_2649_);
                lean_inc(v___y_2648_);
                lean_inc_ref(v___y_2647_);
                v___x_2685_ = lean_apply_5(
                    v___x_2915__overap_2684_,
                    v___y_2647_,
                    v___y_2648_,
                    v___y_2649_,
                    v___y_2650_,
                    lean_box(0),
                );
                return v___x_2685_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___boxed(
    mut v_msg_2692_: *mut LeanObject,
    mut v___y_2693_: *mut LeanObject,
    mut v___y_2694_: *mut LeanObject,
    mut v___y_2695_: *mut LeanObject,
    mut v___y_2696_: *mut LeanObject,
    mut v___y_2697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2698_: *mut LeanObject = core::ptr::null_mut();
    v_res_2698_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0(v_msg_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
    lean_dec(v___y_2696_);
    lean_dec_ref(v___y_2695_);
    lean_dec(v___y_2694_);
    lean_dec_ref(v___y_2693_);
    return v_res_2698_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(
    mut v_fst_2699_: *mut LeanObject,
    mut v_snd_2700_: *mut LeanObject,
    mut v_fst_2701_: *mut LeanObject,
    mut v_x_2702_: *mut LeanObject,
    mut v___y_2703_: *mut LeanObject,
    mut v___y_2704_: *mut LeanObject,
    mut v___y_2705_: *mut LeanObject,
    mut v___y_2706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    v___x_2708_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2708_, 0, v_fst_2699_);
    lean_ctor_set(v___x_2708_, 1, v_snd_2700_);
    v___x_2709_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2709_, 0, v_fst_2701_);
    lean_ctor_set(v___x_2709_, 1, v___x_2708_);
    v___x_2710_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2710_, 0, v___x_2709_);
    v___x_2711_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2711_, 0, v___x_2710_);
    return v___x_2711_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0___boxed(
    mut v_fst_2712_: *mut LeanObject,
    mut v_snd_2713_: *mut LeanObject,
    mut v_fst_2714_: *mut LeanObject,
    mut v_x_2715_: *mut LeanObject,
    mut v___y_2716_: *mut LeanObject,
    mut v___y_2717_: *mut LeanObject,
    mut v___y_2718_: *mut LeanObject,
    mut v___y_2719_: *mut LeanObject,
    mut v___y_2720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2721_: *mut LeanObject = core::ptr::null_mut();
    v_res_2721_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_2712_, v_snd_2713_, v_fst_2714_, v_x_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
    lean_dec(v___y_2719_);
    lean_dec_ref(v___y_2718_);
    lean_dec(v___y_2717_);
    lean_dec_ref(v___y_2716_);
    lean_dec_ref(v_x_2715_);
    return v_res_2721_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2722_: u8 = 0;
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    v___x_2722_ = 1;
    v___x_2723_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(v___x_2722_);
    return v___x_2723_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    v___x_2727_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__3;
    v___x_2728_ = lean_unsigned_to_nat(6);
    v___x_2729_ = lean_unsigned_to_nat(87);
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
    mut v_targetId_2733_: *mut LeanObject,
    mut v_a_2734_: *mut LeanObject,
    mut v___y_2735_: *mut LeanObject,
    mut v___y_2736_: *mut LeanObject,
    mut v___y_2737_: *mut LeanObject,
    mut v___y_2738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2752_: u8 = 0;
    let mut v_a_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2759_: u8 = 0;
    let mut v_a_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2763_: u8 = 0;
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2767_: u8 = 0;
    let mut v_snd_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2772_: u8 = 0;
    let mut v_fst_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2777_: u8 = 0;
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: u8 = 0;
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2814_: u8 = 0;
    let mut v_fvarId_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2820_: u8 = 0;
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2828_: u8 = 0;
    let mut v_unused_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2830_: u8 = 0;
    let mut v_unused_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_check_2834_: u8 = 0;
    let mut v_persistent_2835_: u8 = 0;
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: u8 = 0;
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2848_: u8 = 0;
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2860_: u8 = 0;
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: u8 = 0;
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2872_: u8 = 0;
    let mut v_unused_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: u8 = 0;
    let mut v___x_2887_: u8 = 0;
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2890_: u8 = 0;
    let mut v_fvarId_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2896_: u8 = 0;
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2904_: u8 = 0;
    let mut v_unused_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2906_: u8 = 0;
    let mut v_unused_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2910_: u8 = 0;
    let mut v_isSharedCheck_2911_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_2768_ = lean_ctor_get(v_a_2734_, 1);
                v_fst_2769_ = lean_ctor_get(v_a_2734_, 0);
                v_isSharedCheck_2911_ = (!lean_is_exclusive(v_a_2734_)) as u8;
                if v_isSharedCheck_2911_ == 0 {
                    v___x_2771_ = v_a_2734_;
                    v_isShared_2772_ = v_isSharedCheck_2911_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_snd_2768_);
                    lean_inc(v_fst_2769_);
                    lean_dec(v_a_2734_);
                    v___x_2771_ = lean_box(0);
                    v_isShared_2772_ = v_isSharedCheck_2911_;
                    state = 7;
                    continue;
                }
            }
            1 => {
                v___x_2744_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2744_, 0, v___y_2743_);
                lean_ctor_set(v___x_2744_, 1, v___y_2741_);
                v___x_2745_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2745_, 0, v___y_2742_);
                lean_ctor_set(v___x_2745_, 1, v___x_2744_);
                v_a_2734_ = v___x_2745_;
                state = 0;
                continue;
            }
            2 => {
                if lean_obj_tag(v___y_2748_) == 0 {
                    v_a_2749_ = lean_ctor_get(v___y_2748_, 0);
                    v_isSharedCheck_2759_ = (!lean_is_exclusive(v___y_2748_)) as u8;
                    if v_isSharedCheck_2759_ == 0 {
                        v___x_2751_ = v___y_2748_;
                        v_isShared_2752_ = v_isSharedCheck_2759_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2749_);
                        lean_dec(v___y_2748_);
                        v___x_2751_ = lean_box(0);
                        v_isShared_2752_ = v_isSharedCheck_2759_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_2760_ = lean_ctor_get(v___y_2748_, 0);
                    v_isSharedCheck_2767_ = (!lean_is_exclusive(v___y_2748_)) as u8;
                    if v_isSharedCheck_2767_ == 0 {
                        v___x_2762_ = v___y_2748_;
                        v_isShared_2763_ = v_isSharedCheck_2767_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2760_);
                        lean_dec(v___y_2748_);
                        v___x_2762_ = lean_box(0);
                        v_isShared_2763_ = v_isSharedCheck_2767_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if lean_obj_tag(v_a_2749_) == 0 {
                    v_a_2753_ = lean_ctor_get(v_a_2749_, 0);
                    lean_inc(v_a_2753_);
                    lean_dec_ref_known(v_a_2749_, 1);
                    if v_isShared_2752_ == 0 {
                        lean_ctor_set(v___x_2751_, 0, v_a_2753_);
                        v___x_2755_ = v___x_2751_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_a_2753_);
                        v___x_2755_ = v_reuseFailAlloc_2756_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2751_);
                    v_a_2757_ = lean_ctor_get(v_a_2749_, 0);
                    lean_inc(v_a_2757_);
                    lean_dec_ref_known(v_a_2749_, 1);
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
                    v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
                    v___x_2765_ = v_reuseFailAlloc_2766_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2765_;
            }
            7 => {
                v_fst_2773_ = lean_ctor_get(v_snd_2768_, 0);
                v_snd_2774_ = lean_ctor_get(v_snd_2768_, 1);
                v_isSharedCheck_2910_ = (!lean_is_exclusive(v_snd_2768_)) as u8;
                if v_isSharedCheck_2910_ == 0 {
                    v___x_2776_ = v_snd_2768_;
                    v_isShared_2777_ = v_isSharedCheck_2910_;
                    state = 8;
                    continue;
                } else {
                    lean_inc(v_snd_2774_);
                    lean_inc(v_fst_2773_);
                    lean_dec(v_snd_2768_);
                    v___x_2776_ = lean_box(0);
                    v_isShared_2777_ = v_isSharedCheck_2910_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2778_ = lean_unsigned_to_nat(2);
                v___x_2779_ = lean_array_get_size(v_fst_2769_);
                v___x_2780_ = lean_nat_dec_le(v___x_2778_, v___x_2779_);
                if v___x_2780_ == 0 {
                    if v_isShared_2777_ == 0 {
                        v___x_2782_ = v___x_2776_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_fst_2773_);
                        lean_ctor_set(v_reuseFailAlloc_2787_, 1, v_snd_2774_);
                        v___x_2782_ = v_reuseFailAlloc_2787_;
                        state = 9;
                        continue;
                    }
                } else {
                    v___x_2788_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0);
                    v___x_2789_ = lean_unsigned_to_nat(1);
                    v___x_2790_ = lean_nat_sub(v___x_2779_, v___x_2789_);
                    v___x_2791_ = lean_array_get(v___x_2788_, v_fst_2769_, v___x_2790_);
                    lean_dec(v___x_2790_);
                    match lean_obj_tag(v___x_2791_) {
                        0 => {
                            v_decl_2792_ = lean_ctor_get(v___x_2791_, 0);
                            lean_inc_ref(v_decl_2792_);
                            v_value_2793_ = lean_ctor_get(v_decl_2792_, 3);
                            lean_inc(v_value_2793_);
                            match lean_obj_tag(v_value_2793_) {
                                8 => {
                                    lean_dec_ref_known(v_value_2793_, 3);
                                    lean_dec_ref(v_decl_2792_);
                                    v___x_2794_ = lean_array_pop(v_fst_2769_);
                                    v___x_2795_ = lean_array_push(v_fst_2773_, v___x_2791_);
                                    if v_isShared_2777_ == 0 {
                                        lean_ctor_set(v___x_2776_, 0, v___x_2795_);
                                        v___x_2797_ = v___x_2776_;
                                        state = 11;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 2, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2795_);
                                        lean_ctor_set(v_reuseFailAlloc_2802_, 1, v_snd_2774_);
                                        v___x_2797_ = v_reuseFailAlloc_2802_;
                                        state = 11;
                                        continue;
                                    }
                                }
                                7 => {
                                    lean_dec_ref_known(v_value_2793_, 2);
                                    lean_dec_ref(v_decl_2792_);
                                    v___x_2803_ = lean_array_pop(v_fst_2769_);
                                    v___x_2804_ = lean_array_push(v_fst_2773_, v___x_2791_);
                                    if v_isShared_2777_ == 0 {
                                        lean_ctor_set(v___x_2776_, 0, v___x_2804_);
                                        v___x_2806_ = v___x_2776_;
                                        state = 13;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 2, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2804_);
                                        lean_ctor_set(v_reuseFailAlloc_2811_, 1, v_snd_2774_);
                                        v___x_2806_ = v_reuseFailAlloc_2811_;
                                        state = 13;
                                        continue;
                                    }
                                }
                                _ => {
                                    lean_del_object(v___x_2776_);
                                    lean_del_object(v___x_2771_);
                                    v_isSharedCheck_2830_ = (!lean_is_exclusive(v___x_2791_)) as u8;
                                    if v_isSharedCheck_2830_ == 0 {
                                        v_unused_2831_ = lean_ctor_get(v___x_2791_, 0);
                                        lean_dec(v_unused_2831_);
                                        v___x_2813_ = v___x_2791_;
                                        v_isShared_2814_ = v_isSharedCheck_2830_;
                                        state = 15;
                                        continue;
                                    } else {
                                        lean_dec(v___x_2791_);
                                        v___x_2813_ = lean_box(0);
                                        v_isShared_2814_ = v_isSharedCheck_2830_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            }
                        }
                        7 => {
                            v_fvarId_2832_ = lean_ctor_get(v___x_2791_, 0);
                            v_n_2833_ = lean_ctor_get(v___x_2791_, 1);
                            v_check_2834_ = lean_ctor_get_uint8(
                                v___x_2791_,
                                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                            );
                            v_persistent_2835_ = lean_ctor_get_uint8(
                                v___x_2791_,
                                (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                            );
                            v___x_2836_ = lean_unsigned_to_nat(0);
                            v___x_2837_ = lean_nat_dec_lt(v___x_2836_, v_n_2833_);
                            if v___x_2837_ == 0 {
                                lean_dec_ref_known(v___x_2791_, 2);
                                lean_del_object(v___x_2776_);
                                lean_dec(v_snd_2774_);
                                lean_dec(v_fst_2773_);
                                lean_del_object(v___x_2771_);
                                lean_dec(v_fst_2769_);
                                v___x_2838_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4);
                                v___x_2839_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0(v___x_2838_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
                                v___y_2748_ = v___x_2839_;
                                state = 2;
                                continue;
                            } else {
                                v___x_2840_ = lean_nat_sub(v___x_2779_, v___x_2778_);
                                v___x_2841_ = lean_array_get(v___x_2788_, v_fst_2769_, v___x_2840_);
                                lean_dec(v___x_2840_);
                                if lean_obj_tag(v___x_2841_) == 0 {
                                    v_decl_2842_ = lean_ctor_get(v___x_2841_, 0);
                                    lean_inc_ref(v_decl_2842_);
                                    v_value_2843_ = lean_ctor_get(v_decl_2842_, 3);
                                    lean_inc(v_value_2843_);
                                    if lean_obj_tag(v_value_2843_) == 6 {
                                        v_fvarId_2844_ = lean_ctor_get(v_decl_2842_, 0);
                                        lean_inc(v_fvarId_2844_);
                                        lean_dec_ref(v_decl_2842_);
                                        v_i_2845_ = lean_ctor_get(v_value_2843_, 0);
                                        lean_inc(v_i_2845_);
                                        v_var_2846_ = lean_ctor_get(v_value_2843_, 1);
                                        lean_inc(v_var_2846_);
                                        lean_dec_ref_known(v_value_2843_, 2);
                                        v___x_2886_ = l_Lean_instBEqFVarId_beq(
                                            v_fvarId_2844_,
                                            v_fvarId_2832_,
                                        );
                                        lean_dec(v_fvarId_2844_);
                                        if v___x_2886_ == 0 {
                                            lean_dec(v_var_2846_);
                                            v___y_2848_ = v___x_2886_;
                                            state = 19;
                                            continue;
                                        } else {
                                            v___x_2887_ = l_Lean_instBEqFVarId_beq(
                                                v_targetId_2733_,
                                                v_var_2846_,
                                            );
                                            lean_dec(v_var_2846_);
                                            v___y_2848_ = v___x_2887_;
                                            state = 19;
                                            continue;
                                        }
                                    } else {
                                        lean_dec_ref_known(v___x_2791_, 2);
                                        lean_del_object(v___x_2776_);
                                        lean_del_object(v___x_2771_);
                                        v_isSharedCheck_2906_ =
                                            (!lean_is_exclusive(v___x_2841_)) as u8;
                                        if v_isSharedCheck_2906_ == 0 {
                                            v_unused_2907_ = lean_ctor_get(v___x_2841_, 0);
                                            lean_dec(v_unused_2907_);
                                            v___x_2889_ = v___x_2841_;
                                            v_isShared_2890_ = v_isSharedCheck_2906_;
                                            state = 26;
                                            continue;
                                        } else {
                                            lean_dec(v___x_2841_);
                                            v___x_2889_ = lean_box(0);
                                            v_isShared_2890_ = v_isSharedCheck_2906_;
                                            state = 26;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref_known(v___x_2791_, 2);
                                    lean_del_object(v___x_2776_);
                                    lean_del_object(v___x_2771_);
                                    v___x_2908_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_2773_, v_snd_2774_, v_fst_2769_, v___x_2841_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
                                    lean_dec(v___x_2841_);
                                    v___y_2748_ = v___x_2908_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                        _ => {
                            lean_del_object(v___x_2776_);
                            lean_del_object(v___x_2771_);
                            v___x_2909_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_2773_, v_snd_2774_, v_fst_2769_, v___x_2791_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
                            lean_dec(v___x_2791_);
                            v___y_2748_ = v___x_2909_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            9 => {
                if v_isShared_2772_ == 0 {
                    lean_ctor_set(v___x_2771_, 1, v___x_2782_);
                    v___x_2784_ = v___x_2771_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_fst_2769_);
                    lean_ctor_set(v_reuseFailAlloc_2786_, 1, v___x_2782_);
                    v___x_2784_ = v_reuseFailAlloc_2786_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_2785_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2785_, 0, v___x_2784_);
                return v___x_2785_;
            }
            11 => {
                if v_isShared_2772_ == 0 {
                    lean_ctor_set(v___x_2771_, 1, v___x_2797_);
                    lean_ctor_set(v___x_2771_, 0, v___x_2794_);
                    v___x_2799_ = v___x_2771_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2794_);
                    lean_ctor_set(v_reuseFailAlloc_2801_, 1, v___x_2797_);
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
                    lean_ctor_set(v___x_2771_, 1, v___x_2806_);
                    lean_ctor_set(v___x_2771_, 0, v___x_2803_);
                    v___x_2808_ = v___x_2771_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2810_, 0, v___x_2803_);
                    lean_ctor_set(v_reuseFailAlloc_2810_, 1, v___x_2806_);
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
                v_fvarId_2815_ = lean_ctor_get(v_decl_2792_, 0);
                v_binderName_2816_ = lean_ctor_get(v_decl_2792_, 1);
                v_type_2817_ = lean_ctor_get(v_decl_2792_, 2);
                v_isSharedCheck_2828_ = (!lean_is_exclusive(v_decl_2792_)) as u8;
                if v_isSharedCheck_2828_ == 0 {
                    v_unused_2829_ = lean_ctor_get(v_decl_2792_, 3);
                    lean_dec(v_unused_2829_);
                    v___x_2819_ = v_decl_2792_;
                    v_isShared_2820_ = v_isSharedCheck_2828_;
                    state = 16;
                    continue;
                } else {
                    lean_inc(v_type_2817_);
                    lean_inc(v_binderName_2816_);
                    lean_inc(v_fvarId_2815_);
                    lean_dec(v_decl_2792_);
                    v___x_2819_ = lean_box(0);
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
                    v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_fvarId_2815_);
                    lean_ctor_set(v_reuseFailAlloc_2827_, 1, v_binderName_2816_);
                    lean_ctor_set(v_reuseFailAlloc_2827_, 2, v_type_2817_);
                    lean_ctor_set(v_reuseFailAlloc_2827_, 3, v_value_2793_);
                    v___x_2822_ = v_reuseFailAlloc_2827_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_2814_ == 0 {
                    lean_ctor_set(v___x_2813_, 0, v___x_2822_);
                    v___x_2824_ = v___x_2813_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2822_);
                    v___x_2824_ = v_reuseFailAlloc_2826_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_2825_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_2773_, v_snd_2774_, v_fst_2769_, v___x_2824_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
                lean_dec_ref(v___x_2824_);
                v___y_2748_ = v___x_2825_;
                state = 2;
                continue;
            }
            19 => {
                if v___y_2848_ == 0 {
                    lean_dec(v_i_2845_);
                    lean_dec_ref_known(v___x_2841_, 1);
                    lean_dec_ref_known(v___x_2791_, 2);
                    if v_isShared_2777_ == 0 {
                        v___x_2850_ = v___x_2776_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_fst_2773_);
                        lean_ctor_set(v_reuseFailAlloc_2855_, 1, v_snd_2774_);
                        v___x_2850_ = v_reuseFailAlloc_2855_;
                        state = 20;
                        continue;
                    }
                } else {
                    v___x_2856_ = lean_box(0);
                    v___x_2857_ = lean_array_get_borrowed(v___x_2856_, v_snd_2774_, v_i_2845_);
                    if lean_obj_tag(v___x_2857_) == 0 {
                        lean_inc(v_n_2833_);
                        lean_inc(v_fvarId_2832_);
                        lean_del_object(v___x_2776_);
                        lean_del_object(v___x_2771_);
                        v_isSharedCheck_2872_ = (!lean_is_exclusive(v___x_2791_)) as u8;
                        if v_isSharedCheck_2872_ == 0 {
                            v_unused_2873_ = lean_ctor_get(v___x_2791_, 1);
                            lean_dec(v_unused_2873_);
                            v_unused_2874_ = lean_ctor_get(v___x_2791_, 0);
                            lean_dec(v_unused_2874_);
                            v___x_2859_ = v___x_2791_;
                            v_isShared_2860_ = v_isSharedCheck_2872_;
                            state = 22;
                            continue;
                        } else {
                            lean_dec(v___x_2791_);
                            v___x_2859_ = lean_box(0);
                            v_isShared_2860_ = v_isSharedCheck_2872_;
                            state = 22;
                            continue;
                        }
                    } else {
                        lean_dec(v_i_2845_);
                        v___x_2875_ = lean_array_push(v_fst_2773_, v___x_2791_);
                        v___x_2876_ = lean_array_push(v___x_2875_, v___x_2841_);
                        v___x_2877_ = lean_array_pop(v_fst_2769_);
                        v___x_2878_ = lean_array_pop(v___x_2877_);
                        if v_isShared_2777_ == 0 {
                            lean_ctor_set(v___x_2776_, 0, v___x_2876_);
                            v___x_2880_ = v___x_2776_;
                            state = 24;
                            continue;
                        } else {
                            v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2885_, 0, v___x_2876_);
                            lean_ctor_set(v_reuseFailAlloc_2885_, 1, v_snd_2774_);
                            v___x_2880_ = v_reuseFailAlloc_2885_;
                            state = 24;
                            continue;
                        }
                    }
                }
            }
            20 => {
                if v_isShared_2772_ == 0 {
                    lean_ctor_set(v___x_2771_, 1, v___x_2850_);
                    v___x_2852_ = v___x_2771_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_fst_2769_);
                    lean_ctor_set(v_reuseFailAlloc_2854_, 1, v___x_2850_);
                    v___x_2852_ = v_reuseFailAlloc_2854_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_2853_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2853_, 0, v___x_2852_);
                return v___x_2853_;
            }
            22 => {
                v___x_2861_ = lean_array_pop(v_fst_2769_);
                v___x_2862_ = lean_array_pop(v___x_2861_);
                lean_inc(v_fvarId_2832_);
                v___x_2863_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2863_, 0, v_fvarId_2832_);
                v___x_2864_ = lean_array_set(v_snd_2774_, v_i_2845_, v___x_2863_);
                lean_dec(v_i_2845_);
                v___x_2865_ = lean_array_push(v_fst_2773_, v___x_2841_);
                v___x_2866_ = lean_nat_dec_eq(v_n_2833_, v___x_2789_);
                if v___x_2866_ == 0 {
                    v___x_2867_ = lean_nat_sub(v_n_2833_, v___x_2789_);
                    lean_dec(v_n_2833_);
                    if v_isShared_2860_ == 0 {
                        lean_ctor_set(v___x_2859_, 1, v___x_2867_);
                        v___x_2869_ = v___x_2859_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_2871_ = lean_alloc_ctor(7, 2, (2) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_fvarId_2832_);
                        lean_ctor_set(v_reuseFailAlloc_2871_, 1, v___x_2867_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2871_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                            v_check_2834_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2871_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                            v_persistent_2835_,
                        );
                        v___x_2869_ = v_reuseFailAlloc_2871_;
                        state = 23;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2859_);
                    lean_dec(v_n_2833_);
                    lean_dec(v_fvarId_2832_);
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
                    lean_ctor_set(v___x_2771_, 1, v___x_2880_);
                    lean_ctor_set(v___x_2771_, 0, v___x_2878_);
                    v___x_2882_ = v___x_2771_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2878_);
                    lean_ctor_set(v_reuseFailAlloc_2884_, 1, v___x_2880_);
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
                v_fvarId_2891_ = lean_ctor_get(v_decl_2842_, 0);
                v_binderName_2892_ = lean_ctor_get(v_decl_2842_, 1);
                v_type_2893_ = lean_ctor_get(v_decl_2842_, 2);
                v_isSharedCheck_2904_ = (!lean_is_exclusive(v_decl_2842_)) as u8;
                if v_isSharedCheck_2904_ == 0 {
                    v_unused_2905_ = lean_ctor_get(v_decl_2842_, 3);
                    lean_dec(v_unused_2905_);
                    v___x_2895_ = v_decl_2842_;
                    v_isShared_2896_ = v_isSharedCheck_2904_;
                    state = 27;
                    continue;
                } else {
                    lean_inc(v_type_2893_);
                    lean_inc(v_binderName_2892_);
                    lean_inc(v_fvarId_2891_);
                    lean_dec(v_decl_2842_);
                    v___x_2895_ = lean_box(0);
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
                    v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_fvarId_2891_);
                    lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_binderName_2892_);
                    lean_ctor_set(v_reuseFailAlloc_2903_, 2, v_type_2893_);
                    lean_ctor_set(v_reuseFailAlloc_2903_, 3, v_value_2843_);
                    v___x_2898_ = v_reuseFailAlloc_2903_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_2890_ == 0 {
                    lean_ctor_set(v___x_2889_, 0, v___x_2898_);
                    v___x_2900_ = v___x_2889_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2898_);
                    v___x_2900_ = v_reuseFailAlloc_2902_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                v___x_2901_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_2773_, v_snd_2774_, v_fst_2769_, v___x_2900_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
                lean_dec_ref(v___x_2900_);
                v___y_2748_ = v___x_2901_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___boxed(
    mut v_targetId_2912_: *mut LeanObject,
    mut v_a_2913_: *mut LeanObject,
    mut v___y_2914_: *mut LeanObject,
    mut v___y_2915_: *mut LeanObject,
    mut v___y_2916_: *mut LeanObject,
    mut v___y_2917_: *mut LeanObject,
    mut v___y_2918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2919_: *mut LeanObject = core::ptr::null_mut();
    v_res_2919_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(v_targetId_2912_, v_a_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
    lean_dec(v___y_2917_);
    lean_dec_ref(v___y_2916_);
    lean_dec(v___y_2915_);
    lean_dec_ref(v___y_2914_);
    lean_dec(v_targetId_2912_);
    return v_res_2919_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(
    mut v_nFields_2922_: *mut LeanObject,
    mut v_targetId_2923_: *mut LeanObject,
    mut v_ds_2924_: *mut LeanObject,
    mut v_a_2925_: *mut LeanObject,
    mut v_a_2926_: *mut LeanObject,
    mut v_a_2927_: *mut LeanObject,
    mut v_a_2928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_keep_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mask_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2939_: u8 = 0;
    let mut v_snd_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2946_: u8 = 0;
    let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2955_: u8 = 0;
    let mut v_isSharedCheck_2956_: u8 = 0;
    let mut v_a_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2960_: u8 = 0;
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2964_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_keep_2930_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0;
                v___x_2931_ = lean_box(0);
                v_mask_2932_ = lean_mk_array(v_nFields_2922_, v___x_2931_);
                v___x_2933_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2933_, 0, v_keep_2930_);
                lean_ctor_set(v___x_2933_, 1, v_mask_2932_);
                v___x_2934_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2934_, 0, v_ds_2924_);
                lean_ctor_set(v___x_2934_, 1, v___x_2933_);
                v___x_2935_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(v_targetId_2923_, v___x_2934_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_);
                if lean_obj_tag(v___x_2935_) == 0 {
                    v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
                    v_isSharedCheck_2956_ = (!lean_is_exclusive(v___x_2935_)) as u8;
                    if v_isSharedCheck_2956_ == 0 {
                        v___x_2938_ = v___x_2935_;
                        v_isShared_2939_ = v_isSharedCheck_2956_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2936_);
                        lean_dec(v___x_2935_);
                        v___x_2938_ = lean_box(0);
                        v_isShared_2939_ = v_isSharedCheck_2956_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2957_ = lean_ctor_get(v___x_2935_, 0);
                    v_isSharedCheck_2964_ = (!lean_is_exclusive(v___x_2935_)) as u8;
                    if v_isSharedCheck_2964_ == 0 {
                        v___x_2959_ = v___x_2935_;
                        v_isShared_2960_ = v_isSharedCheck_2964_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2957_);
                        lean_dec(v___x_2935_);
                        v___x_2959_ = lean_box(0);
                        v_isShared_2960_ = v_isSharedCheck_2964_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_2940_ = lean_ctor_get(v_a_2936_, 1);
                lean_inc(v_snd_2940_);
                v_fst_2941_ = lean_ctor_get(v_a_2936_, 0);
                lean_inc(v_fst_2941_);
                lean_dec(v_a_2936_);
                v_fst_2942_ = lean_ctor_get(v_snd_2940_, 0);
                v_snd_2943_ = lean_ctor_get(v_snd_2940_, 1);
                v_isSharedCheck_2955_ = (!lean_is_exclusive(v_snd_2940_)) as u8;
                if v_isSharedCheck_2955_ == 0 {
                    v___x_2945_ = v_snd_2940_;
                    v_isShared_2946_ = v_isSharedCheck_2955_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_2943_);
                    lean_inc(v_fst_2942_);
                    lean_dec(v_snd_2940_);
                    v___x_2945_ = lean_box(0);
                    v_isShared_2946_ = v_isSharedCheck_2955_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2947_ = l_Array_reverse___redArg(v_fst_2942_);
                v___x_2948_ = l_Array_append___redArg(v_fst_2941_, v___x_2947_);
                lean_dec_ref(v___x_2947_);
                if v_isShared_2946_ == 0 {
                    lean_ctor_set(v___x_2945_, 0, v___x_2948_);
                    v___x_2950_ = v___x_2945_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2948_);
                    lean_ctor_set(v_reuseFailAlloc_2954_, 1, v_snd_2943_);
                    v___x_2950_ = v_reuseFailAlloc_2954_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2939_ == 0 {
                    lean_ctor_set(v___x_2938_, 0, v___x_2950_);
                    v___x_2952_ = v___x_2938_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2953_, 0, v___x_2950_);
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
                    v_reuseFailAlloc_2963_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_a_2957_);
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
    mut v_nFields_2965_: *mut LeanObject,
    mut v_targetId_2966_: *mut LeanObject,
    mut v_ds_2967_: *mut LeanObject,
    mut v_a_2968_: *mut LeanObject,
    mut v_a_2969_: *mut LeanObject,
    mut v_a_2970_: *mut LeanObject,
    mut v_a_2971_: *mut LeanObject,
    mut v_a_2972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2973_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2971_);
    lean_dec_ref(v_a_2970_);
    lean_dec(v_a_2969_);
    lean_dec_ref(v_a_2968_);
    lean_dec(v_targetId_2966_);
    return v_res_2973_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1(
    mut v_targetId_2974_: *mut LeanObject,
    mut v_inst_2975_: *mut LeanObject,
    mut v_a_2976_: *mut LeanObject,
    mut v___y_2977_: *mut LeanObject,
    mut v___y_2978_: *mut LeanObject,
    mut v___y_2979_: *mut LeanObject,
    mut v___y_2980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    v___x_2982_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(v_targetId_2974_, v_a_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_);
    return v___x_2982_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___boxed(
    mut v_targetId_2983_: *mut LeanObject,
    mut v_inst_2984_: *mut LeanObject,
    mut v_a_2985_: *mut LeanObject,
    mut v___y_2986_: *mut LeanObject,
    mut v___y_2987_: *mut LeanObject,
    mut v___y_2988_: *mut LeanObject,
    mut v___y_2989_: *mut LeanObject,
    mut v___y_2990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2991_: *mut LeanObject = core::ptr::null_mut();
    v_res_2991_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1(v_targetId_2983_, v_inst_2984_, v_a_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
    lean_dec(v___y_2989_);
    lean_dec_ref(v___y_2988_);
    lean_dec(v___y_2987_);
    lean_dec_ref(v___y_2986_);
    lean_dec(v_targetId_2983_);
    return v_res_2991_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(
    mut v_discr_3008_: *mut LeanObject,
    mut v_discrType_3009_: *mut LeanObject,
    mut v_resultType_3010_: *mut LeanObject,
    mut v_t_3011_: *mut LeanObject,
    mut v_e_3012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    v___x_3014_ = l_Lean_Expr_getAppFn(v_discrType_3009_);
    v___x_3015_ = l_Lean_Expr_constName_x21(v___x_3014_);
    lean_dec_ref(v___x_3014_);
    v___x_3016_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__3;
    v___x_3017_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3017_, 0, v___x_3016_);
    lean_ctor_set(v___x_3017_, 1, v_e_3012_);
    v___x_3018_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__6;
    v___x_3019_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3019_, 0, v___x_3018_);
    lean_ctor_set(v___x_3019_, 1, v_t_3011_);
    v___x_3020_ = lean_unsigned_to_nat(2);
    v___x_3021_ = lean_mk_empty_array_with_capacity(v___x_3020_);
    v___x_3022_ = lean_array_push(v___x_3021_, v___x_3017_);
    v___x_3023_ = lean_array_push(v___x_3022_, v___x_3019_);
    v___x_3024_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3024_, 0, v___x_3015_);
    lean_ctor_set(v___x_3024_, 1, v_resultType_3010_);
    lean_ctor_set(v___x_3024_, 2, v_discr_3008_);
    lean_ctor_set(v___x_3024_, 3, v___x_3023_);
    v___x_3025_ = lean_alloc_ctor(4, 1, (0) as u32);
    lean_ctor_set(v___x_3025_, 0, v___x_3024_);
    v___x_3026_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3026_, 0, v___x_3025_);
    return v___x_3026_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___boxed(
    mut v_discr_3027_: *mut LeanObject,
    mut v_discrType_3028_: *mut LeanObject,
    mut v_resultType_3029_: *mut LeanObject,
    mut v_t_3030_: *mut LeanObject,
    mut v_e_3031_: *mut LeanObject,
    mut v_a_3032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3033_: *mut LeanObject = core::ptr::null_mut();
    v_res_3033_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(
            v_discr_3027_,
            v_discrType_3028_,
            v_resultType_3029_,
            v_t_3030_,
            v_e_3031_,
        );
    lean_dec_ref(v_discrType_3028_);
    return v_res_3033_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf(
    mut v_discr_3034_: *mut LeanObject,
    mut v_discrType_3035_: *mut LeanObject,
    mut v_resultType_3036_: *mut LeanObject,
    mut v_t_3037_: *mut LeanObject,
    mut v_e_3038_: *mut LeanObject,
    mut v_a_3039_: *mut LeanObject,
    mut v_a_3040_: *mut LeanObject,
    mut v_a_3041_: *mut LeanObject,
    mut v_a_3042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_discr_3045_: *mut LeanObject,
    mut v_discrType_3046_: *mut LeanObject,
    mut v_resultType_3047_: *mut LeanObject,
    mut v_t_3048_: *mut LeanObject,
    mut v_e_3049_: *mut LeanObject,
    mut v_a_3050_: *mut LeanObject,
    mut v_a_3051_: *mut LeanObject,
    mut v_a_3052_: *mut LeanObject,
    mut v_a_3053_: *mut LeanObject,
    mut v_a_3054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3055_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3053_);
    lean_dec_ref(v_a_3052_);
    lean_dec(v_a_3051_);
    lean_dec_ref(v_a_3050_);
    lean_dec_ref(v_discrType_3046_);
    return v_res_3055_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__0(
    mut v_msg_3056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    v___x_3057_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0);
    v___x_3058_ = lean_panic_fn_borrowed(v___x_3057_, v_msg_3056_);
    return v___x_3058_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2()
-> *mut LeanObject {
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    v___x_3061_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1;
    v___x_3062_ = lean_unsigned_to_nat(11);
    v___x_3063_ = lean_unsigned_to_nat(138);
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
    mut v_targetId_3067_: *mut LeanObject,
    mut v_sz_3068_: usize,
    mut v_i_3069_: usize,
    mut v_bs_3070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3071_: u8 = 0;
    let mut v_v_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: usize = 0;
    let mut v___x_3078_: usize = 0;
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3085_: u8 = 0;
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3089_: u8 = 0;
    let mut v_unused_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3097_: u8 = 0;
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3101_: u8 = 0;
    let mut v_unused_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3107_: u8 = 0;
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3111_: u8 = 0;
    let mut v_unused_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3071_ = lean_usize_dec_lt(v_i_3069_, v_sz_3068_);
                if v___x_3071_ == 0 {
                    lean_dec(v_targetId_3067_);
                    return v_bs_3070_;
                } else {
                    v_v_3072_ = lean_array_uget(v_bs_3070_, v_i_3069_);
                    v___x_3073_ = lean_unsigned_to_nat(0);
                    v_bs_x27_3074_ = lean_array_uset(v_bs_3070_, v_i_3069_, v___x_3073_);
                    match lean_obj_tag(v_v_3072_) {
                        3 => {
                            v_i_3081_ = lean_ctor_get(v_v_3072_, 1);
                            v_y_3082_ = lean_ctor_get(v_v_3072_, 2);
                            v_isSharedCheck_3089_ = (!lean_is_exclusive(v_v_3072_)) as u8;
                            if v_isSharedCheck_3089_ == 0 {
                                v_unused_3090_ = lean_ctor_get(v_v_3072_, 0);
                                lean_dec(v_unused_3090_);
                                v___x_3084_ = v_v_3072_;
                                v_isShared_3085_ = v_isSharedCheck_3089_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_y_3082_);
                                lean_inc(v_i_3081_);
                                lean_dec(v_v_3072_);
                                v___x_3084_ = lean_box(0);
                                v_isShared_3085_ = v_isSharedCheck_3089_;
                                state = 2;
                                continue;
                            }
                        }
                        5 => {
                            v_i_3091_ = lean_ctor_get(v_v_3072_, 1);
                            v_offset_3092_ = lean_ctor_get(v_v_3072_, 2);
                            v_y_3093_ = lean_ctor_get(v_v_3072_, 3);
                            v_ty_3094_ = lean_ctor_get(v_v_3072_, 4);
                            v_isSharedCheck_3101_ = (!lean_is_exclusive(v_v_3072_)) as u8;
                            if v_isSharedCheck_3101_ == 0 {
                                v_unused_3102_ = lean_ctor_get(v_v_3072_, 0);
                                lean_dec(v_unused_3102_);
                                v___x_3096_ = v_v_3072_;
                                v_isShared_3097_ = v_isSharedCheck_3101_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_ty_3094_);
                                lean_inc(v_y_3093_);
                                lean_inc(v_offset_3092_);
                                lean_inc(v_i_3091_);
                                lean_dec(v_v_3072_);
                                v___x_3096_ = lean_box(0);
                                v_isShared_3097_ = v_isSharedCheck_3101_;
                                state = 4;
                                continue;
                            }
                        }
                        4 => {
                            v_i_3103_ = lean_ctor_get(v_v_3072_, 1);
                            v_y_3104_ = lean_ctor_get(v_v_3072_, 2);
                            v_isSharedCheck_3111_ = (!lean_is_exclusive(v_v_3072_)) as u8;
                            if v_isSharedCheck_3111_ == 0 {
                                v_unused_3112_ = lean_ctor_get(v_v_3072_, 0);
                                lean_dec(v_unused_3112_);
                                v___x_3106_ = v_v_3072_;
                                v_isShared_3107_ = v_isSharedCheck_3111_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_y_3104_);
                                lean_inc(v_i_3103_);
                                lean_dec(v_v_3072_);
                                v___x_3106_ = lean_box(0);
                                v_isShared_3107_ = v_isSharedCheck_3111_;
                                state = 6;
                                continue;
                            }
                        }
                        _ => {
                            lean_dec(v_v_3072_);
                            v___x_3113_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2);
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
                lean_inc(v_targetId_3067_);
                if v_isShared_3085_ == 0 {
                    lean_ctor_set(v___x_3084_, 0, v_targetId_3067_);
                    v___x_3087_ = v___x_3084_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3088_ = lean_alloc_ctor(3, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_targetId_3067_);
                    lean_ctor_set(v_reuseFailAlloc_3088_, 1, v_i_3081_);
                    lean_ctor_set(v_reuseFailAlloc_3088_, 2, v_y_3082_);
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
                lean_inc(v_targetId_3067_);
                if v_isShared_3097_ == 0 {
                    lean_ctor_set(v___x_3096_, 0, v_targetId_3067_);
                    v___x_3099_ = v___x_3096_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3100_ = lean_alloc_ctor(5, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_targetId_3067_);
                    lean_ctor_set(v_reuseFailAlloc_3100_, 1, v_i_3091_);
                    lean_ctor_set(v_reuseFailAlloc_3100_, 2, v_offset_3092_);
                    lean_ctor_set(v_reuseFailAlloc_3100_, 3, v_y_3093_);
                    lean_ctor_set(v_reuseFailAlloc_3100_, 4, v_ty_3094_);
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
                lean_inc(v_targetId_3067_);
                if v_isShared_3107_ == 0 {
                    lean_ctor_set(v___x_3106_, 0, v_targetId_3067_);
                    v___x_3109_ = v___x_3106_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3110_ = lean_alloc_ctor(4, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_targetId_3067_);
                    lean_ctor_set(v_reuseFailAlloc_3110_, 1, v_i_3103_);
                    lean_ctor_set(v_reuseFailAlloc_3110_, 2, v_y_3104_);
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
    mut v_targetId_3115_: *mut LeanObject,
    mut v_sz_3116_: *mut LeanObject,
    mut v_i_3117_: *mut LeanObject,
    mut v_bs_3118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3119_: usize = 0;
    let mut v_i_boxed_3120_: usize = 0;
    let mut v_res_3121_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3119_ = lean_unbox_usize(v_sz_3116_);
    lean_dec(v_sz_3116_);
    v_i_boxed_3120_ = lean_unbox_usize(v_i_3117_);
    lean_dec(v_i_3117_);
    v_res_3121_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(v_targetId_3115_, v_sz_boxed_3119_, v_i_boxed_3120_, v_bs_3118_);
    return v_res_3121_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(
    mut v_targetId_3122_: *mut LeanObject,
    mut v_sets_3123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_3125_: usize = 0;
    let mut v___x_3126_: usize = 0;
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    v_sz_3125_ = lean_array_size(v_sets_3123_);
    v___x_3126_ = 0usize;
    v___x_3127_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(v_targetId_3122_, v_sz_3125_, v___x_3126_, v_sets_3123_);
    v___x_3128_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3128_, 0, v___x_3127_);
    return v___x_3128_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg___boxed(
    mut v_targetId_3129_: *mut LeanObject,
    mut v_sets_3130_: *mut LeanObject,
    mut v_a_3131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3132_: *mut LeanObject = core::ptr::null_mut();
    v_res_3132_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(
            v_targetId_3129_,
            v_sets_3130_,
        );
    return v_res_3132_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets(
    mut v_targetId_3133_: *mut LeanObject,
    mut v_sets_3134_: *mut LeanObject,
    mut v_a_3135_: *mut LeanObject,
    mut v_a_3136_: *mut LeanObject,
    mut v_a_3137_: *mut LeanObject,
    mut v_a_3138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    v___x_3140_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(
            v_targetId_3133_,
            v_sets_3134_,
        );
    return v___x_3140_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___boxed(
    mut v_targetId_3141_: *mut LeanObject,
    mut v_sets_3142_: *mut LeanObject,
    mut v_a_3143_: *mut LeanObject,
    mut v_a_3144_: *mut LeanObject,
    mut v_a_3145_: *mut LeanObject,
    mut v_a_3146_: *mut LeanObject,
    mut v_a_3147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3148_: *mut LeanObject = core::ptr::null_mut();
    v_res_3148_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets(
        v_targetId_3141_,
        v_sets_3142_,
        v_a_3143_,
        v_a_3144_,
        v_a_3145_,
        v_a_3146_,
    );
    lean_dec(v_a_3146_);
    lean_dec_ref(v_a_3145_);
    lean_dec(v_a_3144_);
    lean_dec_ref(v_a_3143_);
    return v_res_3148_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(
    mut v_fvarId_3149_: *mut LeanObject,
    mut v_i_3150_: *mut LeanObject,
    mut v_y_3151_: *mut LeanObject,
    mut v_a_3152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3154_: u8 = 0;
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: u8 = 0;
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3163_: u8 = 0;
    let mut v_val_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: u8 = 0;
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: u8 = 0;
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: u8 = 0;
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: u8 = 0;
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3187_: u8 = 0;
    let mut v_a_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3191_: u8 = 0;
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3195_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_y_3151_) == 0 {
                    v___x_3154_ = 0;
                    v___x_3155_ = lean_box((v___x_3154_) as usize);
                    v___x_3156_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3156_, 0, v___x_3155_);
                    return v___x_3156_;
                } else {
                    v_fvarId_3157_ = lean_ctor_get(v_y_3151_, 0);
                    v___x_3158_ = 1;
                    v___x_3159_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(
                        v___x_3158_,
                        v_fvarId_3157_,
                        v_a_3152_,
                    );
                    if lean_obj_tag(v___x_3159_) == 0 {
                        v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
                        v_isSharedCheck_3187_ = (!lean_is_exclusive(v___x_3159_)) as u8;
                        if v_isSharedCheck_3187_ == 0 {
                            v___x_3162_ = v___x_3159_;
                            v_isShared_3163_ = v_isSharedCheck_3187_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3160_);
                            lean_dec(v___x_3159_);
                            v___x_3162_ = lean_box(0);
                            v_isShared_3163_ = v_isSharedCheck_3187_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3188_ = lean_ctor_get(v___x_3159_, 0);
                        v_isSharedCheck_3195_ = (!lean_is_exclusive(v___x_3159_)) as u8;
                        if v_isSharedCheck_3195_ == 0 {
                            v___x_3190_ = v___x_3159_;
                            v_isShared_3191_ = v_isSharedCheck_3195_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_3188_);
                            lean_dec(v___x_3159_);
                            v___x_3190_ = lean_box(0);
                            v_isShared_3191_ = v_isSharedCheck_3195_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3160_) == 1 {
                    v_val_3164_ = lean_ctor_get(v_a_3160_, 0);
                    lean_inc(v_val_3164_);
                    lean_dec_ref_known(v_a_3160_, 1);
                    if lean_obj_tag(v_val_3164_) == 6 {
                        v_i_3165_ = lean_ctor_get(v_val_3164_, 0);
                        lean_inc(v_i_3165_);
                        v_var_3166_ = lean_ctor_get(v_val_3164_, 1);
                        lean_inc(v_var_3166_);
                        lean_dec_ref_known(v_val_3164_, 2);
                        v___x_3167_ = lean_nat_dec_eq(v_i_3150_, v_i_3165_);
                        lean_dec(v_i_3165_);
                        if v___x_3167_ == 0 {
                            lean_dec(v_var_3166_);
                            v___x_3168_ = lean_box((v___x_3167_) as usize);
                            if v_isShared_3163_ == 0 {
                                lean_ctor_set(v___x_3162_, 0, v___x_3168_);
                                v___x_3170_ = v___x_3162_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3171_, 0, v___x_3168_);
                                v___x_3170_ = v_reuseFailAlloc_3171_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_3172_ = l_Lean_instBEqFVarId_beq(v_fvarId_3149_, v_var_3166_);
                            lean_dec(v_var_3166_);
                            v___x_3173_ = lean_box((v___x_3172_) as usize);
                            if v_isShared_3163_ == 0 {
                                lean_ctor_set(v___x_3162_, 0, v___x_3173_);
                                v___x_3175_ = v___x_3162_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3176_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3176_, 0, v___x_3173_);
                                v___x_3175_ = v_reuseFailAlloc_3176_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_val_3164_);
                        v___x_3177_ = 0;
                        v___x_3178_ = lean_box((v___x_3177_) as usize);
                        if v_isShared_3163_ == 0 {
                            lean_ctor_set(v___x_3162_, 0, v___x_3178_);
                            v___x_3180_ = v___x_3162_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3181_, 0, v___x_3178_);
                            v___x_3180_ = v_reuseFailAlloc_3181_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_3160_);
                    v___x_3182_ = 0;
                    v___x_3183_ = lean_box((v___x_3182_) as usize);
                    if v_isShared_3163_ == 0 {
                        lean_ctor_set(v___x_3162_, 0, v___x_3183_);
                        v___x_3185_ = v___x_3162_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3186_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3186_, 0, v___x_3183_);
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
                    v_reuseFailAlloc_3194_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_a_3188_);
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
    mut v_fvarId_3196_: *mut LeanObject,
    mut v_i_3197_: *mut LeanObject,
    mut v_y_3198_: *mut LeanObject,
    mut v_a_3199_: *mut LeanObject,
    mut v_a_3200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3201_: *mut LeanObject = core::ptr::null_mut();
    v_res_3201_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(
            v_fvarId_3196_,
            v_i_3197_,
            v_y_3198_,
            v_a_3199_,
        );
    lean_dec(v_a_3199_);
    lean_dec(v_y_3198_);
    lean_dec(v_i_3197_);
    lean_dec(v_fvarId_3196_);
    return v_res_3201_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset(
    mut v_fvarId_3202_: *mut LeanObject,
    mut v_i_3203_: *mut LeanObject,
    mut v_y_3204_: *mut LeanObject,
    mut v_a_3205_: *mut LeanObject,
    mut v_a_3206_: *mut LeanObject,
    mut v_a_3207_: *mut LeanObject,
    mut v_a_3208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_fvarId_3211_: *mut LeanObject,
    mut v_i_3212_: *mut LeanObject,
    mut v_y_3213_: *mut LeanObject,
    mut v_a_3214_: *mut LeanObject,
    mut v_a_3215_: *mut LeanObject,
    mut v_a_3216_: *mut LeanObject,
    mut v_a_3217_: *mut LeanObject,
    mut v_a_3218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3219_: *mut LeanObject = core::ptr::null_mut();
    v_res_3219_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset(
        v_fvarId_3211_,
        v_i_3212_,
        v_y_3213_,
        v_a_3214_,
        v_a_3215_,
        v_a_3216_,
        v_a_3217_,
    );
    lean_dec(v_a_3217_);
    lean_dec_ref(v_a_3216_);
    lean_dec(v_a_3215_);
    lean_dec_ref(v_a_3214_);
    lean_dec(v_y_3213_);
    lean_dec(v_i_3212_);
    lean_dec(v_fvarId_3211_);
    return v_res_3219_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(
    mut v_fvarId_3220_: *mut LeanObject,
    mut v_i_3221_: *mut LeanObject,
    mut v_y_3222_: *mut LeanObject,
    mut v_a_3223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3225_: u8 = 0;
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3230_: u8 = 0;
    let mut v_val_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: u8 = 0;
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: u8 = 0;
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: u8 = 0;
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: u8 = 0;
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3254_: u8 = 0;
    let mut v_a_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3258_: u8 = 0;
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3261_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_3226_) == 0 {
                    v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
                    v_isSharedCheck_3254_ = (!lean_is_exclusive(v___x_3226_)) as u8;
                    if v_isSharedCheck_3254_ == 0 {
                        v___x_3229_ = v___x_3226_;
                        v_isShared_3230_ = v_isSharedCheck_3254_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3227_);
                        lean_dec(v___x_3226_);
                        v___x_3229_ = lean_box(0);
                        v_isShared_3230_ = v_isSharedCheck_3254_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3255_ = lean_ctor_get(v___x_3226_, 0);
                    v_isSharedCheck_3262_ = (!lean_is_exclusive(v___x_3226_)) as u8;
                    if v_isSharedCheck_3262_ == 0 {
                        v___x_3257_ = v___x_3226_;
                        v_isShared_3258_ = v_isSharedCheck_3262_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3255_);
                        lean_dec(v___x_3226_);
                        v___x_3257_ = lean_box(0);
                        v_isShared_3258_ = v_isSharedCheck_3262_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3227_) == 1 {
                    v_val_3231_ = lean_ctor_get(v_a_3227_, 0);
                    lean_inc(v_val_3231_);
                    lean_dec_ref_known(v_a_3227_, 1);
                    if lean_obj_tag(v_val_3231_) == 7 {
                        v_i_3232_ = lean_ctor_get(v_val_3231_, 0);
                        lean_inc(v_i_3232_);
                        v_var_3233_ = lean_ctor_get(v_val_3231_, 1);
                        lean_inc(v_var_3233_);
                        lean_dec_ref_known(v_val_3231_, 2);
                        v___x_3234_ = lean_nat_dec_eq(v_i_3221_, v_i_3232_);
                        lean_dec(v_i_3232_);
                        if v___x_3234_ == 0 {
                            lean_dec(v_var_3233_);
                            v___x_3235_ = lean_box((v___x_3234_) as usize);
                            if v_isShared_3230_ == 0 {
                                lean_ctor_set(v___x_3229_, 0, v___x_3235_);
                                v___x_3237_ = v___x_3229_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3235_);
                                v___x_3237_ = v_reuseFailAlloc_3238_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_3239_ = l_Lean_instBEqFVarId_beq(v_fvarId_3220_, v_var_3233_);
                            lean_dec(v_var_3233_);
                            v___x_3240_ = lean_box((v___x_3239_) as usize);
                            if v_isShared_3230_ == 0 {
                                lean_ctor_set(v___x_3229_, 0, v___x_3240_);
                                v___x_3242_ = v___x_3229_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3243_, 0, v___x_3240_);
                                v___x_3242_ = v_reuseFailAlloc_3243_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_val_3231_);
                        v___x_3244_ = 0;
                        v___x_3245_ = lean_box((v___x_3244_) as usize);
                        if v_isShared_3230_ == 0 {
                            lean_ctor_set(v___x_3229_, 0, v___x_3245_);
                            v___x_3247_ = v___x_3229_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3245_);
                            v___x_3247_ = v_reuseFailAlloc_3248_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_3227_);
                    v___x_3249_ = 0;
                    v___x_3250_ = lean_box((v___x_3249_) as usize);
                    if v_isShared_3230_ == 0 {
                        lean_ctor_set(v___x_3229_, 0, v___x_3250_);
                        v___x_3252_ = v___x_3229_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3253_, 0, v___x_3250_);
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
                    v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3255_);
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
    mut v_fvarId_3263_: *mut LeanObject,
    mut v_i_3264_: *mut LeanObject,
    mut v_y_3265_: *mut LeanObject,
    mut v_a_3266_: *mut LeanObject,
    mut v_a_3267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3268_: *mut LeanObject = core::ptr::null_mut();
    v_res_3268_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(
            v_fvarId_3263_,
            v_i_3264_,
            v_y_3265_,
            v_a_3266_,
        );
    lean_dec(v_a_3266_);
    lean_dec(v_y_3265_);
    lean_dec(v_i_3264_);
    lean_dec(v_fvarId_3263_);
    return v_res_3268_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset(
    mut v_fvarId_3269_: *mut LeanObject,
    mut v_i_3270_: *mut LeanObject,
    mut v_y_3271_: *mut LeanObject,
    mut v_a_3272_: *mut LeanObject,
    mut v_a_3273_: *mut LeanObject,
    mut v_a_3274_: *mut LeanObject,
    mut v_a_3275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_fvarId_3278_: *mut LeanObject,
    mut v_i_3279_: *mut LeanObject,
    mut v_y_3280_: *mut LeanObject,
    mut v_a_3281_: *mut LeanObject,
    mut v_a_3282_: *mut LeanObject,
    mut v_a_3283_: *mut LeanObject,
    mut v_a_3284_: *mut LeanObject,
    mut v_a_3285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3286_: *mut LeanObject = core::ptr::null_mut();
    v_res_3286_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset(
        v_fvarId_3278_,
        v_i_3279_,
        v_y_3280_,
        v_a_3281_,
        v_a_3282_,
        v_a_3283_,
        v_a_3284_,
    );
    lean_dec(v_a_3284_);
    lean_dec_ref(v_a_3283_);
    lean_dec(v_a_3282_);
    lean_dec_ref(v_a_3281_);
    lean_dec(v_y_3280_);
    lean_dec(v_i_3279_);
    lean_dec(v_fvarId_3278_);
    return v_res_3286_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(
    mut v_fvarId_3287_: *mut LeanObject,
    mut v_i_3288_: *mut LeanObject,
    mut v_offset_3289_: *mut LeanObject,
    mut v_y_3290_: *mut LeanObject,
    mut v_a_3291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3293_: u8 = 0;
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3298_: u8 = 0;
    let mut v_val_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3304_: u8 = 0;
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: u8 = 0;
    let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: u8 = 0;
    let mut v___x_3315_: u8 = 0;
    let mut v___x_3316_: u8 = 0;
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: u8 = 0;
    let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3326_: u8 = 0;
    let mut v_a_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3330_: u8 = 0;
    let mut v___x_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3333_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_3294_) == 0 {
                    v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
                    v_isSharedCheck_3326_ = (!lean_is_exclusive(v___x_3294_)) as u8;
                    if v_isSharedCheck_3326_ == 0 {
                        v___x_3297_ = v___x_3294_;
                        v_isShared_3298_ = v_isSharedCheck_3326_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3295_);
                        lean_dec(v___x_3294_);
                        v___x_3297_ = lean_box(0);
                        v_isShared_3298_ = v_isSharedCheck_3326_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3327_ = lean_ctor_get(v___x_3294_, 0);
                    v_isSharedCheck_3334_ = (!lean_is_exclusive(v___x_3294_)) as u8;
                    if v_isSharedCheck_3334_ == 0 {
                        v___x_3329_ = v___x_3294_;
                        v_isShared_3330_ = v_isSharedCheck_3334_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3327_);
                        lean_dec(v___x_3294_);
                        v___x_3329_ = lean_box(0);
                        v_isShared_3330_ = v_isSharedCheck_3334_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3295_) == 1 {
                    v_val_3299_ = lean_ctor_get(v_a_3295_, 0);
                    lean_inc(v_val_3299_);
                    lean_dec_ref_known(v_a_3295_, 1);
                    if lean_obj_tag(v_val_3299_) == 8 {
                        v_n_3300_ = lean_ctor_get(v_val_3299_, 0);
                        lean_inc(v_n_3300_);
                        v_offset_3301_ = lean_ctor_get(v_val_3299_, 1);
                        lean_inc(v_offset_3301_);
                        v_var_3302_ = lean_ctor_get(v_val_3299_, 2);
                        lean_inc(v_var_3302_);
                        lean_dec_ref_known(v_val_3299_, 3);
                        v___x_3314_ = lean_nat_dec_eq(v_i_3288_, v_n_3300_);
                        lean_dec(v_n_3300_);
                        if v___x_3314_ == 0 {
                            lean_dec(v_offset_3301_);
                            v___y_3304_ = v___x_3314_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3315_ = lean_nat_dec_eq(v_offset_3289_, v_offset_3301_);
                            lean_dec(v_offset_3301_);
                            v___y_3304_ = v___x_3315_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_3299_);
                        v___x_3316_ = 0;
                        v___x_3317_ = lean_box((v___x_3316_) as usize);
                        if v_isShared_3298_ == 0 {
                            lean_ctor_set(v___x_3297_, 0, v___x_3317_);
                            v___x_3319_ = v___x_3297_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3320_, 0, v___x_3317_);
                            v___x_3319_ = v_reuseFailAlloc_3320_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_3295_);
                    v___x_3321_ = 0;
                    v___x_3322_ = lean_box((v___x_3321_) as usize);
                    if v_isShared_3298_ == 0 {
                        lean_ctor_set(v___x_3297_, 0, v___x_3322_);
                        v___x_3324_ = v___x_3297_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3322_);
                        v___x_3324_ = v_reuseFailAlloc_3325_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v___y_3304_ == 0 {
                    lean_dec(v_var_3302_);
                    v___x_3305_ = lean_box((v___y_3304_) as usize);
                    if v_isShared_3298_ == 0 {
                        lean_ctor_set(v___x_3297_, 0, v___x_3305_);
                        v___x_3307_ = v___x_3297_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3308_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3308_, 0, v___x_3305_);
                        v___x_3307_ = v_reuseFailAlloc_3308_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_3309_ = l_Lean_instBEqFVarId_beq(v_fvarId_3287_, v_var_3302_);
                    lean_dec(v_var_3302_);
                    v___x_3310_ = lean_box((v___x_3309_) as usize);
                    if v_isShared_3298_ == 0 {
                        lean_ctor_set(v___x_3297_, 0, v___x_3310_);
                        v___x_3312_ = v___x_3297_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3310_);
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
                    v_reuseFailAlloc_3333_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_a_3327_);
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
    mut v_fvarId_3335_: *mut LeanObject,
    mut v_i_3336_: *mut LeanObject,
    mut v_offset_3337_: *mut LeanObject,
    mut v_y_3338_: *mut LeanObject,
    mut v_a_3339_: *mut LeanObject,
    mut v_a_3340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3341_: *mut LeanObject = core::ptr::null_mut();
    v_res_3341_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(
            v_fvarId_3335_,
            v_i_3336_,
            v_offset_3337_,
            v_y_3338_,
            v_a_3339_,
        );
    lean_dec(v_a_3339_);
    lean_dec(v_y_3338_);
    lean_dec(v_offset_3337_);
    lean_dec(v_i_3336_);
    lean_dec(v_fvarId_3335_);
    return v_res_3341_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset(
    mut v_fvarId_3342_: *mut LeanObject,
    mut v_i_3343_: *mut LeanObject,
    mut v_offset_3344_: *mut LeanObject,
    mut v_y_3345_: *mut LeanObject,
    mut v_a_3346_: *mut LeanObject,
    mut v_a_3347_: *mut LeanObject,
    mut v_a_3348_: *mut LeanObject,
    mut v_a_3349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_fvarId_3352_: *mut LeanObject,
    mut v_i_3353_: *mut LeanObject,
    mut v_offset_3354_: *mut LeanObject,
    mut v_y_3355_: *mut LeanObject,
    mut v_a_3356_: *mut LeanObject,
    mut v_a_3357_: *mut LeanObject,
    mut v_a_3358_: *mut LeanObject,
    mut v_a_3359_: *mut LeanObject,
    mut v_a_3360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3361_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3359_);
    lean_dec_ref(v_a_3358_);
    lean_dec(v_a_3357_);
    lean_dec_ref(v_a_3356_);
    lean_dec(v_y_3355_);
    lean_dec(v_offset_3354_);
    lean_dec(v_i_3353_);
    lean_dec(v_fvarId_3352_);
    return v_res_3361_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(
    mut v_msg_3362_: *mut LeanObject,
    mut v___y_3363_: *mut LeanObject,
    mut v___y_3364_: *mut LeanObject,
    mut v___y_3365_: *mut LeanObject,
    mut v___y_3366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3373_: u8 = 0;
    let mut v_toFunctor_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3380_: u8 = 0;
    let mut v___f_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: u8 = 0;
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994__overap_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3402_: u8 = 0;
    let mut v_unused_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3404_: u8 = 0;
    let mut v_unused_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3368_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0);
                v___x_3369_ = l_StateRefT_x27_instMonad___redArg(v___x_3368_);
                v_toApplicative_3370_ = lean_ctor_get(v___x_3369_, 0);
                v_isSharedCheck_3404_ = (!lean_is_exclusive(v___x_3369_)) as u8;
                if v_isSharedCheck_3404_ == 0 {
                    v_unused_3405_ = lean_ctor_get(v___x_3369_, 1);
                    lean_dec(v_unused_3405_);
                    v___x_3372_ = v___x_3369_;
                    v_isShared_3373_ = v_isSharedCheck_3404_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_3370_);
                    lean_dec(v___x_3369_);
                    v___x_3372_ = lean_box(0);
                    v_isShared_3373_ = v_isSharedCheck_3404_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3374_ = lean_ctor_get(v_toApplicative_3370_, 0);
                v_toSeq_3375_ = lean_ctor_get(v_toApplicative_3370_, 2);
                v_toSeqLeft_3376_ = lean_ctor_get(v_toApplicative_3370_, 3);
                v_toSeqRight_3377_ = lean_ctor_get(v_toApplicative_3370_, 4);
                v_isSharedCheck_3402_ = (!lean_is_exclusive(v_toApplicative_3370_)) as u8;
                if v_isSharedCheck_3402_ == 0 {
                    v_unused_3403_ = lean_ctor_get(v_toApplicative_3370_, 1);
                    lean_dec(v_unused_3403_);
                    v___x_3379_ = v_toApplicative_3370_;
                    v_isShared_3380_ = v_isSharedCheck_3402_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_3377_);
                    lean_inc(v_toSeqLeft_3376_);
                    lean_inc(v_toSeq_3375_);
                    lean_inc(v_toFunctor_3374_);
                    lean_dec(v_toApplicative_3370_);
                    v___x_3379_ = lean_box(0);
                    v_isShared_3380_ = v_isSharedCheck_3402_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_3381_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1;
                v___f_3382_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2;
                lean_inc_ref(v_toFunctor_3374_);
                v___f_3383_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3383_, 0, v_toFunctor_3374_);
                v___f_3384_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3384_, 0, v_toFunctor_3374_);
                v___x_3385_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3385_, 0, v___f_3383_);
                lean_ctor_set(v___x_3385_, 1, v___f_3384_);
                v___f_3386_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3386_, 0, v_toSeqRight_3377_);
                v___f_3387_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3387_, 0, v_toSeqLeft_3376_);
                v___f_3388_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3388_, 0, v_toSeq_3375_);
                if v_isShared_3380_ == 0 {
                    lean_ctor_set(v___x_3379_, 4, v___f_3386_);
                    lean_ctor_set(v___x_3379_, 3, v___f_3387_);
                    lean_ctor_set(v___x_3379_, 2, v___f_3388_);
                    lean_ctor_set(v___x_3379_, 1, v___f_3381_);
                    lean_ctor_set(v___x_3379_, 0, v___x_3385_);
                    v___x_3390_ = v___x_3379_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3401_, 0, v___x_3385_);
                    lean_ctor_set(v_reuseFailAlloc_3401_, 1, v___f_3381_);
                    lean_ctor_set(v_reuseFailAlloc_3401_, 2, v___f_3388_);
                    lean_ctor_set(v_reuseFailAlloc_3401_, 3, v___f_3387_);
                    lean_ctor_set(v_reuseFailAlloc_3401_, 4, v___f_3386_);
                    v___x_3390_ = v_reuseFailAlloc_3401_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3373_ == 0 {
                    lean_ctor_set(v___x_3372_, 1, v___f_3382_);
                    lean_ctor_set(v___x_3372_, 0, v___x_3390_);
                    v___x_3392_ = v___x_3372_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3400_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3400_, 0, v___x_3390_);
                    lean_ctor_set(v_reuseFailAlloc_3400_, 1, v___f_3382_);
                    v___x_3392_ = v_reuseFailAlloc_3400_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3393_ = l_StateRefT_x27_instMonad___redArg(v___x_3392_);
                v___x_3394_ = 0;
                v___x_3395_ = lean_box((v___x_3394_) as usize);
                v___x_3396_ = l_instInhabitedOfMonad___redArg(v___x_3393_, v___x_3395_);
                v___f_3397_ = lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_3397_, 0, v___x_3396_);
                v___x_994__overap_3398_ = lean_panic_fn_borrowed(v___f_3397_, v_msg_3362_);
                lean_dec_ref(v___f_3397_);
                lean_inc(v___y_3366_);
                lean_inc_ref(v___y_3365_);
                lean_inc(v___y_3364_);
                lean_inc_ref(v___y_3363_);
                v___x_3399_ = lean_apply_5(
                    v___x_994__overap_3398_,
                    v___y_3363_,
                    v___y_3364_,
                    v___y_3365_,
                    v___y_3366_,
                    lean_box(0),
                );
                return v___x_3399_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0___boxed(
    mut v_msg_3406_: *mut LeanObject,
    mut v___y_3407_: *mut LeanObject,
    mut v___y_3408_: *mut LeanObject,
    mut v___y_3409_: *mut LeanObject,
    mut v___y_3410_: *mut LeanObject,
    mut v___y_3411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3412_: *mut LeanObject = core::ptr::null_mut();
    v_res_3412_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(v_msg_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
    lean_dec(v___y_3410_);
    lean_dec_ref(v___y_3409_);
    lean_dec(v___y_3408_);
    lean_dec_ref(v___y_3407_);
    return v_res_3412_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut LeanObject = core::ptr::null_mut();
    v___x_3414_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1;
    v___x_3415_ = lean_unsigned_to_nat(13);
    v___x_3416_ = lean_unsigned_to_nat(174);
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
    mut v_selfId_3420_: *mut LeanObject,
    mut v_as_3421_: *mut LeanObject,
    mut v_sz_3422_: usize,
    mut v_i_3423_: usize,
    mut v_b_3424_: *mut LeanObject,
    mut v___y_3425_: *mut LeanObject,
    mut v___y_3426_: *mut LeanObject,
    mut v___y_3427_: *mut LeanObject,
    mut v___y_3428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: usize = 0;
    let mut v___x_3433_: usize = 0;
    let mut v___x_3435_: u8 = 0;
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3441_: u8 = 0;
    let mut v_a_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: u8 = 0;
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3458_: u8 = 0;
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3462_: u8 = 0;
    let mut v_i_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3475_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3435_ = lean_usize_dec_lt(v_i_3423_, v_sz_3422_);
                if v___x_3435_ == 0 {
                    v___x_3436_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3436_, 0, v_b_3424_);
                    return v___x_3436_;
                } else {
                    v_fst_3437_ = lean_ctor_get(v_b_3424_, 0);
                    v_snd_3438_ = lean_ctor_get(v_b_3424_, 1);
                    v_isSharedCheck_3475_ = (!lean_is_exclusive(v_b_3424_)) as u8;
                    if v_isSharedCheck_3475_ == 0 {
                        v___x_3440_ = v_b_3424_;
                        v_isShared_3441_ = v_isSharedCheck_3475_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_3438_);
                        lean_inc(v_fst_3437_);
                        lean_dec(v_b_3424_);
                        v___x_3440_ = lean_box(0);
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
                match lean_obj_tag(v_a_3442_) {
                    3 => {
                        v_i_3463_ = lean_ctor_get(v_a_3442_, 1);
                        v_y_3464_ = lean_ctor_get(v_a_3442_, 2);
                        v___x_3465_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_selfId_3420_, v_i_3463_, v_y_3464_, v___y_3426_);
                        v___y_3444_ = v___x_3465_;
                        state = 3;
                        continue;
                    }
                    4 => {
                        v_i_3466_ = lean_ctor_get(v_a_3442_, 1);
                        v_y_3467_ = lean_ctor_get(v_a_3442_, 2);
                        v___x_3468_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(v_selfId_3420_, v_i_3466_, v_y_3467_, v___y_3426_);
                        v___y_3444_ = v___x_3468_;
                        state = 3;
                        continue;
                    }
                    5 => {
                        v_i_3469_ = lean_ctor_get(v_a_3442_, 1);
                        v_offset_3470_ = lean_ctor_get(v_a_3442_, 2);
                        v_y_3471_ = lean_ctor_get(v_a_3442_, 3);
                        v___x_3472_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(v_selfId_3420_, v_i_3469_, v_offset_3470_, v_y_3471_, v___y_3426_);
                        v___y_3444_ = v___x_3472_;
                        state = 3;
                        continue;
                    }
                    _ => {
                        v___x_3473_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1);
                        v___x_3474_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(v___x_3473_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
                        v___y_3444_ = v___x_3474_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if lean_obj_tag(v___y_3444_) == 0 {
                    v_a_3445_ = lean_ctor_get(v___y_3444_, 0);
                    lean_inc(v_a_3445_);
                    lean_dec_ref_known(v___y_3444_, 1);
                    v___x_3446_ = (lean_unbox(v_a_3445_) as u8);
                    lean_dec(v_a_3445_);
                    if v___x_3446_ == 0 {
                        lean_inc(v_a_3442_);
                        v___x_3447_ = lean_array_push(v_fst_3437_, v_a_3442_);
                        if v_isShared_3441_ == 0 {
                            lean_ctor_set(v___x_3440_, 0, v___x_3447_);
                            v___x_3449_ = v___x_3440_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3450_, 0, v___x_3447_);
                            lean_ctor_set(v_reuseFailAlloc_3450_, 1, v_snd_3438_);
                            v___x_3449_ = v_reuseFailAlloc_3450_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_inc(v_a_3442_);
                        v___x_3451_ = lean_array_push(v_snd_3438_, v_a_3442_);
                        if v_isShared_3441_ == 0 {
                            lean_ctor_set(v___x_3440_, 1, v___x_3451_);
                            v___x_3453_ = v___x_3440_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_fst_3437_);
                            lean_ctor_set(v_reuseFailAlloc_3454_, 1, v___x_3451_);
                            v___x_3453_ = v_reuseFailAlloc_3454_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3440_);
                    lean_dec(v_snd_3438_);
                    lean_dec(v_fst_3437_);
                    v_a_3455_ = lean_ctor_get(v___y_3444_, 0);
                    v_isSharedCheck_3462_ = (!lean_is_exclusive(v___y_3444_)) as u8;
                    if v_isSharedCheck_3462_ == 0 {
                        v___x_3457_ = v___y_3444_;
                        v_isShared_3458_ = v_isSharedCheck_3462_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3455_);
                        lean_dec(v___y_3444_);
                        v___x_3457_ = lean_box(0);
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
                    v_reuseFailAlloc_3461_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_a_3455_);
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
    mut v_selfId_3476_: *mut LeanObject,
    mut v_as_3477_: *mut LeanObject,
    mut v_sz_3478_: *mut LeanObject,
    mut v_i_3479_: *mut LeanObject,
    mut v_b_3480_: *mut LeanObject,
    mut v___y_3481_: *mut LeanObject,
    mut v___y_3482_: *mut LeanObject,
    mut v___y_3483_: *mut LeanObject,
    mut v___y_3484_: *mut LeanObject,
    mut v___y_3485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3486_: usize = 0;
    let mut v_i_boxed_3487_: usize = 0;
    let mut v_res_3488_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3486_ = lean_unbox_usize(v_sz_3478_);
    lean_dec(v_sz_3478_);
    v_i_boxed_3487_ = lean_unbox_usize(v_i_3479_);
    lean_dec(v_i_3479_);
    v_res_3488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(v_selfId_3476_, v_as_3477_, v_sz_boxed_3486_, v_i_boxed_3487_, v_b_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
    lean_dec(v___y_3484_);
    lean_dec_ref(v___y_3483_);
    lean_dec(v___y_3482_);
    lean_dec_ref(v___y_3481_);
    lean_dec_ref(v_as_3477_);
    lean_dec(v_selfId_3476_);
    return v_res_3488_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(
    mut v_selfId_3491_: *mut LeanObject,
    mut v_sets_3492_: *mut LeanObject,
    mut v_a_3493_: *mut LeanObject,
    mut v_a_3494_: *mut LeanObject,
    mut v_a_3495_: *mut LeanObject,
    mut v_a_3496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3499_: usize = 0;
    let mut v___x_3500_: usize = 0;
    let mut v___x_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3505_: u8 = 0;
    let mut v_fst_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3510_: u8 = 0;
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3516_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_3501_) == 0 {
                    v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
                    v_isSharedCheck_3518_ = (!lean_is_exclusive(v___x_3501_)) as u8;
                    if v_isSharedCheck_3518_ == 0 {
                        v___x_3504_ = v___x_3501_;
                        v_isShared_3505_ = v_isSharedCheck_3518_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3502_);
                        lean_dec(v___x_3501_);
                        v___x_3504_ = lean_box(0);
                        v_isShared_3505_ = v_isSharedCheck_3518_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_3501_;
                }
            }
            1 => {
                v_fst_3506_ = lean_ctor_get(v_a_3502_, 0);
                v_snd_3507_ = lean_ctor_get(v_a_3502_, 1);
                v_isSharedCheck_3517_ = (!lean_is_exclusive(v_a_3502_)) as u8;
                if v_isSharedCheck_3517_ == 0 {
                    v___x_3509_ = v_a_3502_;
                    v_isShared_3510_ = v_isSharedCheck_3517_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_3507_);
                    lean_inc(v_fst_3506_);
                    lean_dec(v_a_3502_);
                    v___x_3509_ = lean_box(0);
                    v_isShared_3510_ = v_isSharedCheck_3517_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_3510_ == 0 {
                    lean_ctor_set(v___x_3509_, 1, v_fst_3506_);
                    lean_ctor_set(v___x_3509_, 0, v_snd_3507_);
                    v___x_3512_ = v___x_3509_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_snd_3507_);
                    lean_ctor_set(v_reuseFailAlloc_3516_, 1, v_fst_3506_);
                    v___x_3512_ = v_reuseFailAlloc_3516_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3505_ == 0 {
                    lean_ctor_set(v___x_3504_, 0, v___x_3512_);
                    v___x_3514_ = v___x_3504_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3515_, 0, v___x_3512_);
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
    mut v_selfId_3519_: *mut LeanObject,
    mut v_sets_3520_: *mut LeanObject,
    mut v_a_3521_: *mut LeanObject,
    mut v_a_3522_: *mut LeanObject,
    mut v_a_3523_: *mut LeanObject,
    mut v_a_3524_: *mut LeanObject,
    mut v_a_3525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3526_: *mut LeanObject = core::ptr::null_mut();
    v_res_3526_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(
            v_selfId_3519_,
            v_sets_3520_,
            v_a_3521_,
            v_a_3522_,
            v_a_3523_,
            v_a_3524_,
        );
    lean_dec(v_a_3524_);
    lean_dec_ref(v_a_3523_);
    lean_dec(v_a_3522_);
    lean_dec_ref(v_a_3521_);
    lean_dec_ref(v_sets_3520_);
    lean_dec(v_selfId_3519_);
    return v_res_3526_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(
    mut v_target_3527_: *mut LeanObject,
    mut v_a_3528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3534_: u8 = 0;
    let mut v_fvarId_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: u8 = 0;
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: u8 = 0;
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3549_: u8 = 0;
    let mut v_unused_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3554_: u8 = 0;
    let mut v_fvarId_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: u8 = 0;
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: u8 = 0;
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3569_: u8 = 0;
    let mut v_unused_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3574_: u8 = 0;
    let mut v_fvarId_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: u8 = 0;
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: u8 = 0;
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3589_: u8 = 0;
    let mut v_unused_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3594_: u8 = 0;
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3599_: u8 = 0;
    let mut v_unused_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_3530_ = lean_ctor_get(v_a_3528_, 1);
                lean_inc(v_snd_3530_);
                match lean_obj_tag(v_snd_3530_) {
                    7 => {
                        v_fst_3531_ = lean_ctor_get(v_a_3528_, 0);
                        v_isSharedCheck_3549_ = (!lean_is_exclusive(v_a_3528_)) as u8;
                        if v_isSharedCheck_3549_ == 0 {
                            v_unused_3550_ = lean_ctor_get(v_a_3528_, 1);
                            lean_dec(v_unused_3550_);
                            v___x_3533_ = v_a_3528_;
                            v_isShared_3534_ = v_isSharedCheck_3549_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_fst_3531_);
                            lean_dec(v_a_3528_);
                            v___x_3533_ = lean_box(0);
                            v_isShared_3534_ = v_isSharedCheck_3549_;
                            state = 1;
                            continue;
                        }
                    }
                    9 => {
                        v_fst_3551_ = lean_ctor_get(v_a_3528_, 0);
                        v_isSharedCheck_3569_ = (!lean_is_exclusive(v_a_3528_)) as u8;
                        if v_isSharedCheck_3569_ == 0 {
                            v_unused_3570_ = lean_ctor_get(v_a_3528_, 1);
                            lean_dec(v_unused_3570_);
                            v___x_3553_ = v_a_3528_;
                            v_isShared_3554_ = v_isSharedCheck_3569_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_fst_3551_);
                            lean_dec(v_a_3528_);
                            v___x_3553_ = lean_box(0);
                            v_isShared_3554_ = v_isSharedCheck_3569_;
                            state = 4;
                            continue;
                        }
                    }
                    8 => {
                        v_fst_3571_ = lean_ctor_get(v_a_3528_, 0);
                        v_isSharedCheck_3589_ = (!lean_is_exclusive(v_a_3528_)) as u8;
                        if v_isSharedCheck_3589_ == 0 {
                            v_unused_3590_ = lean_ctor_get(v_a_3528_, 1);
                            lean_dec(v_unused_3590_);
                            v___x_3573_ = v_a_3528_;
                            v_isShared_3574_ = v_isSharedCheck_3589_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_fst_3571_);
                            lean_dec(v_a_3528_);
                            v___x_3573_ = lean_box(0);
                            v_isShared_3574_ = v_isSharedCheck_3589_;
                            state = 7;
                            continue;
                        }
                    }
                    _ => {
                        v_fst_3591_ = lean_ctor_get(v_a_3528_, 0);
                        v_isSharedCheck_3599_ = (!lean_is_exclusive(v_a_3528_)) as u8;
                        if v_isSharedCheck_3599_ == 0 {
                            v_unused_3600_ = lean_ctor_get(v_a_3528_, 1);
                            lean_dec(v_unused_3600_);
                            v___x_3593_ = v_a_3528_;
                            v_isShared_3594_ = v_isSharedCheck_3599_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_fst_3591_);
                            lean_dec(v_a_3528_);
                            v___x_3593_ = lean_box(0);
                            v_isShared_3594_ = v_isSharedCheck_3599_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fvarId_3535_ = lean_ctor_get(v_snd_3530_, 0);
                v_k_3536_ = lean_ctor_get(v_snd_3530_, 3);
                v___x_3537_ = l_Lean_instBEqFVarId_beq(v_target_3527_, v_fvarId_3535_);
                if v___x_3537_ == 0 {
                    if v_isShared_3534_ == 0 {
                        v___x_3539_ = v___x_3533_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_fst_3531_);
                        lean_ctor_set(v_reuseFailAlloc_3541_, 1, v_snd_3530_);
                        v___x_3539_ = v_reuseFailAlloc_3541_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_k_3536_);
                    v___x_3542_ = 1;
                    v___x_3543_ =
                        l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_3542_, v_snd_3530_);
                    lean_dec_ref_known(v_snd_3530_, 4);
                    v___x_3544_ = lean_array_push(v_fst_3531_, v___x_3543_);
                    if v_isShared_3534_ == 0 {
                        lean_ctor_set(v___x_3533_, 1, v_k_3536_);
                        lean_ctor_set(v___x_3533_, 0, v___x_3544_);
                        v___x_3546_ = v___x_3533_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3544_);
                        lean_ctor_set(v_reuseFailAlloc_3548_, 1, v_k_3536_);
                        v___x_3546_ = v_reuseFailAlloc_3548_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3540_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3540_, 0, v___x_3539_);
                return v___x_3540_;
            }
            3 => {
                v_a_3528_ = v___x_3546_;
                state = 0;
                continue;
            }
            4 => {
                v_fvarId_3555_ = lean_ctor_get(v_snd_3530_, 0);
                v_k_3556_ = lean_ctor_get(v_snd_3530_, 5);
                v___x_3557_ = l_Lean_instBEqFVarId_beq(v_target_3527_, v_fvarId_3555_);
                if v___x_3557_ == 0 {
                    if v_isShared_3554_ == 0 {
                        v___x_3559_ = v___x_3553_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_fst_3551_);
                        lean_ctor_set(v_reuseFailAlloc_3561_, 1, v_snd_3530_);
                        v___x_3559_ = v_reuseFailAlloc_3561_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_k_3556_);
                    v___x_3562_ = 1;
                    v___x_3563_ =
                        l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_3562_, v_snd_3530_);
                    lean_dec_ref_known(v_snd_3530_, 6);
                    v___x_3564_ = lean_array_push(v_fst_3551_, v___x_3563_);
                    if v_isShared_3554_ == 0 {
                        lean_ctor_set(v___x_3553_, 1, v_k_3556_);
                        lean_ctor_set(v___x_3553_, 0, v___x_3564_);
                        v___x_3566_ = v___x_3553_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3568_, 0, v___x_3564_);
                        lean_ctor_set(v_reuseFailAlloc_3568_, 1, v_k_3556_);
                        v___x_3566_ = v_reuseFailAlloc_3568_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                v___x_3560_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3560_, 0, v___x_3559_);
                return v___x_3560_;
            }
            6 => {
                v_a_3528_ = v___x_3566_;
                state = 0;
                continue;
            }
            7 => {
                v_fvarId_3575_ = lean_ctor_get(v_snd_3530_, 0);
                v_k_3576_ = lean_ctor_get(v_snd_3530_, 3);
                v___x_3577_ = l_Lean_instBEqFVarId_beq(v_target_3527_, v_fvarId_3575_);
                if v___x_3577_ == 0 {
                    if v_isShared_3574_ == 0 {
                        v___x_3579_ = v___x_3573_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3581_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_fst_3571_);
                        lean_ctor_set(v_reuseFailAlloc_3581_, 1, v_snd_3530_);
                        v___x_3579_ = v_reuseFailAlloc_3581_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_k_3576_);
                    v___x_3582_ = 1;
                    v___x_3583_ =
                        l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_3582_, v_snd_3530_);
                    lean_dec_ref_known(v_snd_3530_, 4);
                    v___x_3584_ = lean_array_push(v_fst_3571_, v___x_3583_);
                    if v_isShared_3574_ == 0 {
                        lean_ctor_set(v___x_3573_, 1, v_k_3576_);
                        lean_ctor_set(v___x_3573_, 0, v___x_3584_);
                        v___x_3586_ = v___x_3573_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3584_);
                        lean_ctor_set(v_reuseFailAlloc_3588_, 1, v_k_3576_);
                        v___x_3586_ = v_reuseFailAlloc_3588_;
                        state = 9;
                        continue;
                    }
                }
            }
            8 => {
                v___x_3580_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3580_, 0, v___x_3579_);
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
                    v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_fst_3591_);
                    lean_ctor_set(v_reuseFailAlloc_3598_, 1, v_snd_3530_);
                    v___x_3596_ = v_reuseFailAlloc_3598_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_3597_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3597_, 0, v___x_3596_);
                return v___x_3597_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg___boxed(
    mut v_target_3601_: *mut LeanObject,
    mut v_a_3602_: *mut LeanObject,
    mut v___y_3603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3604_: *mut LeanObject = core::ptr::null_mut();
    v_res_3604_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_3601_, v_a_3602_);
    lean_dec(v_target_3601_);
    return v_res_3604_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(
    mut v_target_3605_: *mut LeanObject,
    mut v_k_3606_: *mut LeanObject,
    mut v_a_3607_: *mut LeanObject,
    mut v_a_3608_: *mut LeanObject,
    mut v_a_3609_: *mut LeanObject,
    mut v_a_3610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sets_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3618_: u8 = 0;
    let mut v_fst_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3623_: u8 = 0;
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3630_: u8 = 0;
    let mut v_isSharedCheck_3631_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sets_3612_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0;
                v___x_3613_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3613_, 0, v_sets_3612_);
                lean_ctor_set(v___x_3613_, 1, v_k_3606_);
                v___x_3614_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_3605_, v___x_3613_);
                if lean_obj_tag(v___x_3614_) == 0 {
                    v_a_3615_ = lean_ctor_get(v___x_3614_, 0);
                    v_isSharedCheck_3631_ = (!lean_is_exclusive(v___x_3614_)) as u8;
                    if v_isSharedCheck_3631_ == 0 {
                        v___x_3617_ = v___x_3614_;
                        v_isShared_3618_ = v_isSharedCheck_3631_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3615_);
                        lean_dec(v___x_3614_);
                        v___x_3617_ = lean_box(0);
                        v_isShared_3618_ = v_isSharedCheck_3631_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_3614_;
                }
            }
            1 => {
                v_fst_3619_ = lean_ctor_get(v_a_3615_, 0);
                v_snd_3620_ = lean_ctor_get(v_a_3615_, 1);
                v_isSharedCheck_3630_ = (!lean_is_exclusive(v_a_3615_)) as u8;
                if v_isSharedCheck_3630_ == 0 {
                    v___x_3622_ = v_a_3615_;
                    v_isShared_3623_ = v_isSharedCheck_3630_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_3620_);
                    lean_inc(v_fst_3619_);
                    lean_dec(v_a_3615_);
                    v___x_3622_ = lean_box(0);
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
                    v_reuseFailAlloc_3629_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_fst_3619_);
                    lean_ctor_set(v_reuseFailAlloc_3629_, 1, v_snd_3620_);
                    v___x_3625_ = v_reuseFailAlloc_3629_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3618_ == 0 {
                    lean_ctor_set(v___x_3617_, 0, v___x_3625_);
                    v___x_3627_ = v___x_3617_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3628_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3628_, 0, v___x_3625_);
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
    mut v_target_3632_: *mut LeanObject,
    mut v_k_3633_: *mut LeanObject,
    mut v_a_3634_: *mut LeanObject,
    mut v_a_3635_: *mut LeanObject,
    mut v_a_3636_: *mut LeanObject,
    mut v_a_3637_: *mut LeanObject,
    mut v_a_3638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3639_: *mut LeanObject = core::ptr::null_mut();
    v_res_3639_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(
            v_target_3632_,
            v_k_3633_,
            v_a_3634_,
            v_a_3635_,
            v_a_3636_,
            v_a_3637_,
        );
    lean_dec(v_a_3637_);
    lean_dec_ref(v_a_3636_);
    lean_dec(v_a_3635_);
    lean_dec_ref(v_a_3634_);
    lean_dec(v_target_3632_);
    return v_res_3639_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0(
    mut v_target_3640_: *mut LeanObject,
    mut v_inst_3641_: *mut LeanObject,
    mut v_a_3642_: *mut LeanObject,
    mut v___y_3643_: *mut LeanObject,
    mut v___y_3644_: *mut LeanObject,
    mut v___y_3645_: *mut LeanObject,
    mut v___y_3646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    v___x_3648_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_3640_, v_a_3642_);
    return v___x_3648_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___boxed(
    mut v_target_3649_: *mut LeanObject,
    mut v_inst_3650_: *mut LeanObject,
    mut v_a_3651_: *mut LeanObject,
    mut v___y_3652_: *mut LeanObject,
    mut v___y_3653_: *mut LeanObject,
    mut v___y_3654_: *mut LeanObject,
    mut v___y_3655_: *mut LeanObject,
    mut v___y_3656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3657_: *mut LeanObject = core::ptr::null_mut();
    v_res_3657_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0(v_target_3649_, v_inst_3650_, v_a_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_);
    lean_dec(v___y_3655_);
    lean_dec_ref(v___y_3654_);
    lean_dec(v___y_3653_);
    lean_dec_ref(v___y_3652_);
    lean_dec(v_target_3649_);
    return v_res_3657_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    v___x_3664_ = lean_box(0);
    v___x_3665_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__3;
    v___x_3666_ = l_Lean_Expr_const___override(v___x_3665_, v___x_3664_);
    return v___x_3666_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(
    mut v_upperBound_3667_: *mut LeanObject,
    mut v_mask_3668_: *mut LeanObject,
    mut v_origAllocId_3669_: *mut LeanObject,
    mut v_a_3670_: *mut LeanObject,
    mut v_b_3671_: *mut LeanObject,
    mut v___y_3672_: *mut LeanObject,
    mut v___y_3673_: *mut LeanObject,
    mut v___y_3674_: *mut LeanObject,
    mut v___y_3675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: u8 = 0;
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: u8 = 0;
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: u8 = 0;
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3702_: u8 = 0;
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3706_: u8 = 0;
    let mut v_a_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3710_: u8 = 0;
    let mut v___x_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3714_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3682_ = lean_nat_dec_lt(v_a_3670_, v_upperBound_3667_);
                if v___x_3682_ == 0 {
                    lean_dec(v_a_3670_);
                    lean_dec(v_origAllocId_3669_);
                    v___x_3683_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3683_, 0, v_b_3671_);
                    return v___x_3683_;
                } else {
                    v___x_3684_ = lean_array_fget_borrowed(v_mask_3668_, v_a_3670_);
                    if lean_obj_tag(v___x_3684_) == 0 {
                        v___x_3685_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__1;
                        v___x_3686_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(
                            v___x_3685_,
                            v___y_3673_,
                        );
                        if lean_obj_tag(v___x_3686_) == 0 {
                            v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
                            lean_inc(v_a_3687_);
                            lean_dec_ref_known(v___x_3686_, 1);
                            v___x_3688_ = 1;
                            v___x_3689_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4);
                            lean_inc(v_origAllocId_3669_);
                            lean_inc(v_a_3670_);
                            v___x_3690_ = lean_alloc_ctor(6, 2, (0) as u32);
                            lean_ctor_set(v___x_3690_, 0, v_a_3670_);
                            lean_ctor_set(v___x_3690_, 1, v_origAllocId_3669_);
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
                            if lean_obj_tag(v___x_3691_) == 0 {
                                v_a_3692_ = lean_ctor_get(v___x_3691_, 0);
                                lean_inc(v_a_3692_);
                                lean_dec_ref_known(v___x_3691_, 1);
                                v_fvarId_3693_ = lean_ctor_get(v_a_3692_, 0);
                                v___x_3694_ = 0;
                                v___x_3695_ = lean_unsigned_to_nat(1);
                                v___x_3696_ = lean_box(0);
                                lean_inc(v_fvarId_3693_);
                                v___x_3697_ = lean_alloc_ctor(12, 4, (2) as u32);
                                lean_ctor_set(v___x_3697_, 0, v_fvarId_3693_);
                                lean_ctor_set(v___x_3697_, 1, v___x_3695_);
                                lean_ctor_set(v___x_3697_, 2, v___x_3696_);
                                lean_ctor_set(v___x_3697_, 3, v_b_3671_);
                                lean_ctor_set_uint8(
                                    v___x_3697_,
                                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                                    v___x_3682_,
                                );
                                lean_ctor_set_uint8(
                                    v___x_3697_,
                                    (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                                    v___x_3694_,
                                );
                                v___x_3698_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_3698_, 0, v_a_3692_);
                                lean_ctor_set(v___x_3698_, 1, v___x_3697_);
                                v_a_3678_ = v___x_3698_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v_b_3671_);
                                lean_dec(v_a_3670_);
                                lean_dec(v_origAllocId_3669_);
                                v_a_3699_ = lean_ctor_get(v___x_3691_, 0);
                                v_isSharedCheck_3706_ = (!lean_is_exclusive(v___x_3691_)) as u8;
                                if v_isSharedCheck_3706_ == 0 {
                                    v___x_3701_ = v___x_3691_;
                                    v_isShared_3702_ = v_isSharedCheck_3706_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_3699_);
                                    lean_dec(v___x_3691_);
                                    v___x_3701_ = lean_box(0);
                                    v_isShared_3702_ = v_isSharedCheck_3706_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_b_3671_);
                            lean_dec(v_a_3670_);
                            lean_dec(v_origAllocId_3669_);
                            v_a_3707_ = lean_ctor_get(v___x_3686_, 0);
                            v_isSharedCheck_3714_ = (!lean_is_exclusive(v___x_3686_)) as u8;
                            if v_isSharedCheck_3714_ == 0 {
                                v___x_3709_ = v___x_3686_;
                                v_isShared_3710_ = v_isSharedCheck_3714_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_3707_);
                                lean_dec(v___x_3686_);
                                v___x_3709_ = lean_box(0);
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
                v___x_3679_ = lean_unsigned_to_nat(1);
                v___x_3680_ = lean_nat_add(v_a_3670_, v___x_3679_);
                lean_dec(v_a_3670_);
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
                    v_reuseFailAlloc_3705_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3699_);
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
                    v_reuseFailAlloc_3713_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_a_3707_);
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
    mut v_upperBound_3715_: *mut LeanObject,
    mut v_mask_3716_: *mut LeanObject,
    mut v_origAllocId_3717_: *mut LeanObject,
    mut v_a_3718_: *mut LeanObject,
    mut v_b_3719_: *mut LeanObject,
    mut v___y_3720_: *mut LeanObject,
    mut v___y_3721_: *mut LeanObject,
    mut v___y_3722_: *mut LeanObject,
    mut v___y_3723_: *mut LeanObject,
    mut v___y_3724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3725_: *mut LeanObject = core::ptr::null_mut();
    v_res_3725_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v_upperBound_3715_, v_mask_3716_, v_origAllocId_3717_, v_a_3718_, v_b_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
    lean_dec(v___y_3723_);
    lean_dec_ref(v___y_3722_);
    lean_dec(v___y_3721_);
    lean_dec_ref(v___y_3720_);
    lean_dec_ref(v_mask_3716_);
    lean_dec(v_upperBound_3715_);
    return v_res_3725_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(
    mut v_origAllocId_3726_: *mut LeanObject,
    mut v_mask_3727_: *mut LeanObject,
    mut v_resetJpId_3728_: *mut LeanObject,
    mut v_isSharedId_3729_: *mut LeanObject,
    mut v_a_3730_: *mut LeanObject,
    mut v_a_3731_: *mut LeanObject,
    mut v_a_3732_: *mut LeanObject,
    mut v_a_3733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_origAllocId_3726_);
    v___x_3735_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3735_, 0, v_origAllocId_3726_);
    v___x_3736_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3736_, 0, v_isSharedId_3729_);
    v___x_3737_ = lean_unsigned_to_nat(0);
    v___x_3738_ = lean_array_get_size(v_mask_3727_);
    v___x_3739_ = lean_unsigned_to_nat(2);
    v___x_3740_ = lean_mk_empty_array_with_capacity(v___x_3739_);
    v___x_3741_ = lean_array_push(v___x_3740_, v___x_3735_);
    v___x_3742_ = lean_array_push(v___x_3741_, v___x_3736_);
    v_code_3743_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v_code_3743_, 0, v_resetJpId_3728_);
    lean_ctor_set(v_code_3743_, 1, v___x_3742_);
    v___x_3744_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v___x_3738_, v_mask_3727_, v_origAllocId_3726_, v___x_3737_, v_code_3743_, v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_);
    return v___x_3744_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath___boxed(
    mut v_origAllocId_3745_: *mut LeanObject,
    mut v_mask_3746_: *mut LeanObject,
    mut v_resetJpId_3747_: *mut LeanObject,
    mut v_isSharedId_3748_: *mut LeanObject,
    mut v_a_3749_: *mut LeanObject,
    mut v_a_3750_: *mut LeanObject,
    mut v_a_3751_: *mut LeanObject,
    mut v_a_3752_: *mut LeanObject,
    mut v_a_3753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3754_: *mut LeanObject = core::ptr::null_mut();
    v_res_3754_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(v_origAllocId_3745_, v_mask_3746_, v_resetJpId_3747_, v_isSharedId_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
    lean_dec(v_a_3752_);
    lean_dec_ref(v_a_3751_);
    lean_dec(v_a_3750_);
    lean_dec_ref(v_a_3749_);
    lean_dec_ref(v_mask_3746_);
    return v_res_3754_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0(
    mut v_upperBound_3755_: *mut LeanObject,
    mut v_mask_3756_: *mut LeanObject,
    mut v_origAllocId_3757_: *mut LeanObject,
    mut v_inst_3758_: *mut LeanObject,
    mut v_R_3759_: *mut LeanObject,
    mut v_a_3760_: *mut LeanObject,
    mut v_b_3761_: *mut LeanObject,
    mut v_c_3762_: *mut LeanObject,
    mut v___y_3763_: *mut LeanObject,
    mut v___y_3764_: *mut LeanObject,
    mut v___y_3765_: *mut LeanObject,
    mut v___y_3766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    v___x_3768_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v_upperBound_3755_, v_mask_3756_, v_origAllocId_3757_, v_a_3760_, v_b_3761_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
    return v___x_3768_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___boxed(
    mut v_upperBound_3769_: *mut LeanObject,
    mut v_mask_3770_: *mut LeanObject,
    mut v_origAllocId_3771_: *mut LeanObject,
    mut v_inst_3772_: *mut LeanObject,
    mut v_R_3773_: *mut LeanObject,
    mut v_a_3774_: *mut LeanObject,
    mut v_b_3775_: *mut LeanObject,
    mut v_c_3776_: *mut LeanObject,
    mut v___y_3777_: *mut LeanObject,
    mut v___y_3778_: *mut LeanObject,
    mut v___y_3779_: *mut LeanObject,
    mut v___y_3780_: *mut LeanObject,
    mut v___y_3781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3782_: *mut LeanObject = core::ptr::null_mut();
    v_res_3782_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0(v_upperBound_3769_, v_mask_3770_, v_origAllocId_3771_, v_inst_3772_, v_R_3773_, v_a_3774_, v_b_3775_, v_c_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
    lean_dec(v___y_3780_);
    lean_dec_ref(v___y_3779_);
    lean_dec(v___y_3778_);
    lean_dec_ref(v___y_3777_);
    lean_dec_ref(v_mask_3770_);
    lean_dec(v_upperBound_3769_);
    return v_res_3782_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(
    mut v_as_3783_: *mut LeanObject,
    mut v_sz_3784_: usize,
    mut v_i_3785_: usize,
    mut v_b_3786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: usize = 0;
    let mut v___x_3791_: usize = 0;
    let mut v___x_3793_: u8 = 0;
    let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: u8 = 0;
    let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3793_ = lean_usize_dec_lt(v_i_3785_, v_sz_3784_);
                if v___x_3793_ == 0 {
                    v___x_3794_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3794_, 0, v_b_3786_);
                    return v___x_3794_;
                } else {
                    v_a_3795_ = lean_array_uget_borrowed(v_as_3783_, v_i_3785_);
                    if lean_obj_tag(v_a_3795_) == 1 {
                        v_val_3796_ = lean_ctor_get(v_a_3795_, 0);
                        v___x_3797_ = lean_unsigned_to_nat(1);
                        v___x_3798_ = 0;
                        lean_inc(v_val_3796_);
                        v___x_3799_ = lean_alloc_ctor(11, 3, (2) as u32);
                        lean_ctor_set(v___x_3799_, 0, v_val_3796_);
                        lean_ctor_set(v___x_3799_, 1, v___x_3797_);
                        lean_ctor_set(v___x_3799_, 2, v_b_3786_);
                        lean_ctor_set_uint8(
                            v___x_3799_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v___x_3793_,
                        );
                        lean_ctor_set_uint8(
                            v___x_3799_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
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
    mut v_as_3800_: *mut LeanObject,
    mut v_sz_3801_: *mut LeanObject,
    mut v_i_3802_: *mut LeanObject,
    mut v_b_3803_: *mut LeanObject,
    mut v___y_3804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3805_: usize = 0;
    let mut v_i_boxed_3806_: usize = 0;
    let mut v_res_3807_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3805_ = lean_unbox_usize(v_sz_3801_);
    lean_dec(v_sz_3801_);
    v_i_boxed_3806_ = lean_unbox_usize(v_i_3802_);
    lean_dec(v_i_3802_);
    v_res_3807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(v_as_3800_, v_sz_boxed_3805_, v_i_boxed_3806_, v_b_3803_);
    lean_dec_ref(v_as_3800_);
    return v_res_3807_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0()
-> *mut LeanObject {
    let mut v___x_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut LeanObject = core::ptr::null_mut();
    v___x_3808_ = lean_box(0);
    v___x_3809_ = lean_unsigned_to_nat(2);
    v___x_3810_ = lean_mk_empty_array_with_capacity(v___x_3809_);
    v___x_3811_ = lean_array_push(v___x_3810_, v___x_3808_);
    return v___x_3811_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(
    mut v_origAllocId_3812_: *mut LeanObject,
    mut v_mask_3813_: *mut LeanObject,
    mut v_resetJpId_3814_: *mut LeanObject,
    mut v_isSharedId_3815_: *mut LeanObject,
    mut v_a_3816_: *mut LeanObject,
    mut v_a_3817_: *mut LeanObject,
    mut v_a_3818_: *mut LeanObject,
    mut v_a_3819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: u8 = 0;
    let mut v___x_3827_: u8 = 0;
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3830_: usize = 0;
    let mut v___x_3831_: usize = 0;
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    v___x_3821_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3821_, 0, v_isSharedId_3815_);
    v___x_3822_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0_once), _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0);
    v___x_3823_ = lean_array_push(v___x_3822_, v___x_3821_);
    v_code_3824_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v_code_3824_, 0, v_resetJpId_3814_);
    lean_ctor_set(v_code_3824_, 1, v___x_3823_);
    v___x_3825_ = lean_unsigned_to_nat(1);
    v___x_3826_ = 1;
    v___x_3827_ = 0;
    v___x_3828_ = lean_box(0);
    v_code_3829_ = lean_alloc_ctor(12, 4, (2) as u32);
    lean_ctor_set(v_code_3829_, 0, v_origAllocId_3812_);
    lean_ctor_set(v_code_3829_, 1, v___x_3825_);
    lean_ctor_set(v_code_3829_, 2, v___x_3828_);
    lean_ctor_set(v_code_3829_, 3, v_code_3824_);
    lean_ctor_set_uint8(
        v_code_3829_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v___x_3826_,
    );
    lean_ctor_set_uint8(
        v_code_3829_,
        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
        v___x_3827_,
    );
    v_sz_3830_ = lean_array_size(v_mask_3813_);
    v___x_3831_ = 0usize;
    v___x_3832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(v_mask_3813_, v_sz_3830_, v___x_3831_, v_code_3829_);
    return v___x_3832_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___boxed(
    mut v_origAllocId_3833_: *mut LeanObject,
    mut v_mask_3834_: *mut LeanObject,
    mut v_resetJpId_3835_: *mut LeanObject,
    mut v_isSharedId_3836_: *mut LeanObject,
    mut v_a_3837_: *mut LeanObject,
    mut v_a_3838_: *mut LeanObject,
    mut v_a_3839_: *mut LeanObject,
    mut v_a_3840_: *mut LeanObject,
    mut v_a_3841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3842_: *mut LeanObject = core::ptr::null_mut();
    v_res_3842_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(v_origAllocId_3833_, v_mask_3834_, v_resetJpId_3835_, v_isSharedId_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_);
    lean_dec(v_a_3840_);
    lean_dec_ref(v_a_3839_);
    lean_dec(v_a_3838_);
    lean_dec_ref(v_a_3837_);
    lean_dec_ref(v_mask_3834_);
    return v_res_3842_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0(
    mut v_as_3843_: *mut LeanObject,
    mut v_sz_3844_: usize,
    mut v_i_3845_: usize,
    mut v_b_3846_: *mut LeanObject,
    mut v___y_3847_: *mut LeanObject,
    mut v___y_3848_: *mut LeanObject,
    mut v___y_3849_: *mut LeanObject,
    mut v___y_3850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    v___x_3852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(v_as_3843_, v_sz_3844_, v_i_3845_, v_b_3846_);
    return v___x_3852_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___boxed(
    mut v_as_3853_: *mut LeanObject,
    mut v_sz_3854_: *mut LeanObject,
    mut v_i_3855_: *mut LeanObject,
    mut v_b_3856_: *mut LeanObject,
    mut v___y_3857_: *mut LeanObject,
    mut v___y_3858_: *mut LeanObject,
    mut v___y_3859_: *mut LeanObject,
    mut v___y_3860_: *mut LeanObject,
    mut v___y_3861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3862_: usize = 0;
    let mut v_i_boxed_3863_: usize = 0;
    let mut v_res_3864_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3862_ = lean_unbox_usize(v_sz_3854_);
    lean_dec(v_sz_3854_);
    v_i_boxed_3863_ = lean_unbox_usize(v_i_3855_);
    lean_dec(v_i_3855_);
    v_res_3864_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0(v_as_3853_, v_sz_boxed_3862_, v_i_boxed_3863_, v_b_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
    lean_dec(v___y_3860_);
    lean_dec_ref(v___y_3859_);
    lean_dec(v___y_3858_);
    lean_dec_ref(v___y_3857_);
    lean_dec_ref(v_as_3853_);
    return v_res_3864_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(
    mut v_upperBound_3865_: *mut LeanObject,
    mut v_args_3866_: *mut LeanObject,
    mut v_origAllocId_3867_: *mut LeanObject,
    mut v_resetTokenId_3868_: *mut LeanObject,
    mut v_a_3869_: *mut LeanObject,
    mut v_b_3870_: *mut LeanObject,
    mut v___y_3871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3873_: u8 = 0;
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: u8 = 0;
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3888_: u8 = 0;
    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3892_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3873_ = lean_nat_dec_lt(v_a_3869_, v_upperBound_3865_);
                if v___x_3873_ == 0 {
                    lean_dec(v_a_3869_);
                    lean_dec(v_resetTokenId_3868_);
                    v___x_3874_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3874_, 0, v_b_3870_);
                    return v___x_3874_;
                } else {
                    v___x_3875_ = lean_array_fget_borrowed(v_args_3866_, v_a_3869_);
                    v___x_3876_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_origAllocId_3867_, v_a_3869_, v___x_3875_, v___y_3871_);
                    if lean_obj_tag(v___x_3876_) == 0 {
                        v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
                        lean_inc(v_a_3877_);
                        lean_dec_ref_known(v___x_3876_, 1);
                        v___x_3883_ = (lean_unbox(v_a_3877_) as u8);
                        lean_dec(v_a_3877_);
                        if v___x_3883_ == 0 {
                            lean_inc(v___x_3875_);
                            lean_inc(v_a_3869_);
                            lean_inc(v_resetTokenId_3868_);
                            v___x_3884_ = lean_alloc_ctor(7, 4, (0) as u32);
                            lean_ctor_set(v___x_3884_, 0, v_resetTokenId_3868_);
                            lean_ctor_set(v___x_3884_, 1, v_a_3869_);
                            lean_ctor_set(v___x_3884_, 2, v___x_3875_);
                            lean_ctor_set(v___x_3884_, 3, v_b_3870_);
                            v_a_3879_ = v___x_3884_;
                            state = 1;
                            continue;
                        } else {
                            v_a_3879_ = v_b_3870_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_b_3870_);
                        lean_dec(v_a_3869_);
                        lean_dec(v_resetTokenId_3868_);
                        v_a_3885_ = lean_ctor_get(v___x_3876_, 0);
                        v_isSharedCheck_3892_ = (!lean_is_exclusive(v___x_3876_)) as u8;
                        if v_isSharedCheck_3892_ == 0 {
                            v___x_3887_ = v___x_3876_;
                            v_isShared_3888_ = v_isSharedCheck_3892_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_3885_);
                            lean_dec(v___x_3876_);
                            v___x_3887_ = lean_box(0);
                            v_isShared_3888_ = v_isSharedCheck_3892_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3880_ = lean_unsigned_to_nat(1);
                v___x_3881_ = lean_nat_add(v_a_3869_, v___x_3880_);
                lean_dec(v_a_3869_);
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
                    v_reuseFailAlloc_3891_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_a_3885_);
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
    mut v_upperBound_3893_: *mut LeanObject,
    mut v_args_3894_: *mut LeanObject,
    mut v_origAllocId_3895_: *mut LeanObject,
    mut v_resetTokenId_3896_: *mut LeanObject,
    mut v_a_3897_: *mut LeanObject,
    mut v_b_3898_: *mut LeanObject,
    mut v___y_3899_: *mut LeanObject,
    mut v___y_3900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3901_: *mut LeanObject = core::ptr::null_mut();
    v_res_3901_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(v_upperBound_3893_, v_args_3894_, v_origAllocId_3895_, v_resetTokenId_3896_, v_a_3897_, v_b_3898_, v___y_3899_);
    lean_dec(v___y_3899_);
    lean_dec(v_origAllocId_3895_);
    lean_dec_ref(v_args_3894_);
    lean_dec(v_upperBound_3893_);
    return v_res_3901_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(
    mut v_resetTokenId_3902_: *mut LeanObject,
    mut v_info_3903_: *mut LeanObject,
    mut v_update_3904_: u8,
    mut v_args_3905_: *mut LeanObject,
    mut v_contJpId_3906_: *mut LeanObject,
    mut v_origAllocId_3907_: *mut LeanObject,
    mut v_a_3908_: *mut LeanObject,
    mut v_a_3909_: *mut LeanObject,
    mut v_a_3910_: *mut LeanObject,
    mut v_a_3911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3924_: u8 = 0;
    let mut v_cidx_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3930_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_n(v_resetTokenId_3902_, 2);
                v___x_3913_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3913_, 0, v_resetTokenId_3902_);
                v___x_3914_ = lean_unsigned_to_nat(0);
                v___x_3915_ = lean_array_get_size(v_args_3905_);
                v___x_3916_ = lean_unsigned_to_nat(1);
                v___x_3917_ = lean_mk_empty_array_with_capacity(v___x_3916_);
                v___x_3918_ = lean_array_push(v___x_3917_, v___x_3913_);
                v_code_3919_ = lean_alloc_ctor(3, 2, (0) as u32);
                lean_ctor_set(v_code_3919_, 0, v_contJpId_3906_);
                lean_ctor_set(v_code_3919_, 1, v___x_3918_);
                v___x_3920_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(v___x_3915_, v_args_3905_, v_origAllocId_3907_, v_resetTokenId_3902_, v___x_3914_, v_code_3919_, v_a_3909_);
                if lean_obj_tag(v___x_3920_) == 0 {
                    if v_update_3904_ == 0 {
                        lean_dec(v_resetTokenId_3902_);
                        return v___x_3920_;
                    } else {
                        v_a_3921_ = lean_ctor_get(v___x_3920_, 0);
                        v_isSharedCheck_3930_ = (!lean_is_exclusive(v___x_3920_)) as u8;
                        if v_isSharedCheck_3930_ == 0 {
                            v___x_3923_ = v___x_3920_;
                            v_isShared_3924_ = v_isSharedCheck_3930_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3921_);
                            lean_dec(v___x_3920_);
                            v___x_3923_ = lean_box(0);
                            v_isShared_3924_ = v_isSharedCheck_3930_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_resetTokenId_3902_);
                    return v___x_3920_;
                }
            }
            1 => {
                v_cidx_3925_ = lean_ctor_get(v_info_3903_, 1);
                lean_inc(v_cidx_3925_);
                v___x_3926_ = lean_alloc_ctor(10, 3, (0) as u32);
                lean_ctor_set(v___x_3926_, 0, v_resetTokenId_3902_);
                lean_ctor_set(v___x_3926_, 1, v_cidx_3925_);
                lean_ctor_set(v___x_3926_, 2, v_a_3921_);
                if v_isShared_3924_ == 0 {
                    lean_ctor_set(v___x_3923_, 0, v___x_3926_);
                    v___x_3928_ = v___x_3923_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3929_, 0, v___x_3926_);
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
    mut v_resetTokenId_3931_: *mut LeanObject,
    mut v_info_3932_: *mut LeanObject,
    mut v_update_3933_: *mut LeanObject,
    mut v_args_3934_: *mut LeanObject,
    mut v_contJpId_3935_: *mut LeanObject,
    mut v_origAllocId_3936_: *mut LeanObject,
    mut v_a_3937_: *mut LeanObject,
    mut v_a_3938_: *mut LeanObject,
    mut v_a_3939_: *mut LeanObject,
    mut v_a_3940_: *mut LeanObject,
    mut v_a_3941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_update_boxed_3942_: u8 = 0;
    let mut v_res_3943_: *mut LeanObject = core::ptr::null_mut();
    v_update_boxed_3942_ = (lean_unbox(v_update_3933_) as u8);
    v_res_3943_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(v_resetTokenId_3931_, v_info_3932_, v_update_boxed_3942_, v_args_3934_, v_contJpId_3935_, v_origAllocId_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_);
    lean_dec(v_a_3940_);
    lean_dec_ref(v_a_3939_);
    lean_dec(v_a_3938_);
    lean_dec_ref(v_a_3937_);
    lean_dec(v_origAllocId_3936_);
    lean_dec_ref(v_args_3934_);
    lean_dec_ref(v_info_3932_);
    return v_res_3943_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0(
    mut v_upperBound_3944_: *mut LeanObject,
    mut v_args_3945_: *mut LeanObject,
    mut v_origAllocId_3946_: *mut LeanObject,
    mut v_resetTokenId_3947_: *mut LeanObject,
    mut v_inst_3948_: *mut LeanObject,
    mut v_R_3949_: *mut LeanObject,
    mut v_a_3950_: *mut LeanObject,
    mut v_b_3951_: *mut LeanObject,
    mut v_c_3952_: *mut LeanObject,
    mut v___y_3953_: *mut LeanObject,
    mut v___y_3954_: *mut LeanObject,
    mut v___y_3955_: *mut LeanObject,
    mut v___y_3956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    v___x_3958_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(v_upperBound_3944_, v_args_3945_, v_origAllocId_3946_, v_resetTokenId_3947_, v_a_3950_, v_b_3951_, v___y_3954_);
    return v___x_3958_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___boxed(
    mut v_upperBound_3959_: *mut LeanObject,
    mut v_args_3960_: *mut LeanObject,
    mut v_origAllocId_3961_: *mut LeanObject,
    mut v_resetTokenId_3962_: *mut LeanObject,
    mut v_inst_3963_: *mut LeanObject,
    mut v_R_3964_: *mut LeanObject,
    mut v_a_3965_: *mut LeanObject,
    mut v_b_3966_: *mut LeanObject,
    mut v_c_3967_: *mut LeanObject,
    mut v___y_3968_: *mut LeanObject,
    mut v___y_3969_: *mut LeanObject,
    mut v___y_3970_: *mut LeanObject,
    mut v___y_3971_: *mut LeanObject,
    mut v___y_3972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3973_: *mut LeanObject = core::ptr::null_mut();
    v_res_3973_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0(v_upperBound_3959_, v_args_3960_, v_origAllocId_3961_, v_resetTokenId_3962_, v_inst_3963_, v_R_3964_, v_a_3965_, v_b_3966_, v_c_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_);
    lean_dec(v___y_3971_);
    lean_dec_ref(v___y_3970_);
    lean_dec(v___y_3969_);
    lean_dec_ref(v___y_3968_);
    lean_dec(v_origAllocId_3961_);
    lean_dec_ref(v_args_3960_);
    lean_dec(v_upperBound_3959_);
    return v_res_3973_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(
    mut v_decl_3977_: *mut LeanObject,
    mut v_info_3978_: *mut LeanObject,
    mut v_args_3979_: *mut LeanObject,
    mut v_contJpId_3980_: *mut LeanObject,
    mut v_selfSets_3981_: *mut LeanObject,
    mut v_a_3982_: *mut LeanObject,
    mut v_a_3983_: *mut LeanObject,
    mut v_a_3984_: *mut LeanObject,
    mut v_a_3985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: u8 = 0;
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4001_: u8 = 0;
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4011_: u8 = 0;
    let mut v_a_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4015_: u8 = 0;
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4019_: u8 = 0;
    let mut v_a_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4023_: u8 = 0;
    let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4027_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3987_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__1;
                v___x_3988_ =
                    l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_3987_, v_a_3983_);
                if lean_obj_tag(v___x_3988_) == 0 {
                    v_a_3989_ = lean_ctor_get(v___x_3988_, 0);
                    lean_inc(v_a_3989_);
                    lean_dec_ref_known(v___x_3988_, 1);
                    v_type_3990_ = lean_ctor_get(v_decl_3977_, 2);
                    lean_inc_ref(v_type_3990_);
                    lean_dec_ref(v_decl_3977_);
                    v___x_3991_ = 1;
                    v___x_3992_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_3992_, 0, v_info_3978_);
                    lean_ctor_set(v___x_3992_, 1, v_args_3979_);
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
                    if lean_obj_tag(v___x_3993_) == 0 {
                        v_a_3994_ = lean_ctor_get(v___x_3993_, 0);
                        lean_inc(v_a_3994_);
                        lean_dec_ref_known(v___x_3993_, 1);
                        v_fvarId_3995_ = lean_ctor_get(v_a_3994_, 0);
                        lean_inc_n(v_fvarId_3995_, 2);
                        v___x_3996_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3996_, 0, v_fvarId_3995_);
                        v___x_3997_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(v_fvarId_3995_, v_selfSets_3981_);
                        v_a_3998_ = lean_ctor_get(v___x_3997_, 0);
                        v_isSharedCheck_4011_ = (!lean_is_exclusive(v___x_3997_)) as u8;
                        if v_isSharedCheck_4011_ == 0 {
                            v___x_4000_ = v___x_3997_;
                            v_isShared_4001_ = v_isSharedCheck_4011_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3998_);
                            lean_dec(v___x_3997_);
                            v___x_4000_ = lean_box(0);
                            v_isShared_4001_ = v_isSharedCheck_4011_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_selfSets_3981_);
                        lean_dec(v_contJpId_3980_);
                        v_a_4012_ = lean_ctor_get(v___x_3993_, 0);
                        v_isSharedCheck_4019_ = (!lean_is_exclusive(v___x_3993_)) as u8;
                        if v_isSharedCheck_4019_ == 0 {
                            v___x_4014_ = v___x_3993_;
                            v_isShared_4015_ = v_isSharedCheck_4019_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4012_);
                            lean_dec(v___x_3993_);
                            v___x_4014_ = lean_box(0);
                            v_isShared_4015_ = v_isSharedCheck_4019_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_selfSets_3981_);
                    lean_dec(v_contJpId_3980_);
                    lean_dec_ref(v_args_3979_);
                    lean_dec_ref(v_info_3978_);
                    lean_dec_ref(v_decl_3977_);
                    v_a_4020_ = lean_ctor_get(v___x_3988_, 0);
                    v_isSharedCheck_4027_ = (!lean_is_exclusive(v___x_3988_)) as u8;
                    if v_isSharedCheck_4027_ == 0 {
                        v___x_4022_ = v___x_3988_;
                        v_isShared_4023_ = v_isSharedCheck_4027_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4020_);
                        lean_dec(v___x_3988_);
                        v___x_4022_ = lean_box(0);
                        v_isShared_4023_ = v_isSharedCheck_4027_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4002_ = lean_unsigned_to_nat(1);
                v___x_4003_ = lean_mk_empty_array_with_capacity(v___x_4002_);
                v___x_4004_ = lean_array_push(v___x_4003_, v___x_3996_);
                v___x_4005_ = lean_alloc_ctor(3, 2, (0) as u32);
                lean_ctor_set(v___x_4005_, 0, v_contJpId_3980_);
                lean_ctor_set(v___x_4005_, 1, v___x_4004_);
                v___x_4006_ =
                    l_Lean_Compiler_LCNF_attachCodeDecls(v___x_3991_, v_a_3998_, v___x_4005_);
                lean_dec(v_a_3998_);
                v___x_4007_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4007_, 0, v_a_3994_);
                lean_ctor_set(v___x_4007_, 1, v___x_4006_);
                if v_isShared_4001_ == 0 {
                    lean_ctor_set(v___x_4000_, 0, v___x_4007_);
                    v___x_4009_ = v___x_4000_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4010_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4010_, 0, v___x_4007_);
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
                    v_reuseFailAlloc_4018_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_a_4012_);
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
                    v_reuseFailAlloc_4026_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_a_4020_);
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
    mut v_decl_4028_: *mut LeanObject,
    mut v_info_4029_: *mut LeanObject,
    mut v_args_4030_: *mut LeanObject,
    mut v_contJpId_4031_: *mut LeanObject,
    mut v_selfSets_4032_: *mut LeanObject,
    mut v_a_4033_: *mut LeanObject,
    mut v_a_4034_: *mut LeanObject,
    mut v_a_4035_: *mut LeanObject,
    mut v_a_4036_: *mut LeanObject,
    mut v_a_4037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4038_: *mut LeanObject = core::ptr::null_mut();
    v_res_4038_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(v_decl_4028_, v_info_4029_, v_args_4030_, v_contJpId_4031_, v_selfSets_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_);
    lean_dec(v_a_4036_);
    lean_dec_ref(v_a_4035_);
    lean_dec(v_a_4034_);
    lean_dec_ref(v_a_4033_);
    return v_res_4038_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(
    mut v_alt_4039_: *mut LeanObject,
    mut v_f_4040_: *mut LeanObject,
    mut v___y_4041_: *mut LeanObject,
    mut v___y_4042_: *mut LeanObject,
    mut v___y_4043_: *mut LeanObject,
    mut v___y_4044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4052_: u8 = 0;
    let mut v___x_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4057_: u8 = 0;
    let mut v_a_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4061_: u8 = 0;
    let mut v___x_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4065_: u8 = 0;
    let mut v_code_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_alt_4039_) {
                0 => {
                    v_code_4066_ = lean_ctor_get(v_alt_4039_, 2);
                    lean_inc_ref(v_code_4066_);
                    v___y_4047_ = v_code_4066_;
                    state = 1;
                    continue;
                }
                1 => {
                    v_code_4067_ = lean_ctor_get(v_alt_4039_, 1);
                    lean_inc_ref(v_code_4067_);
                    v___y_4047_ = v_code_4067_;
                    state = 1;
                    continue;
                }
                _ => {
                    v_code_4068_ = lean_ctor_get(v_alt_4039_, 0);
                    lean_inc_ref(v_code_4068_);
                    v___y_4047_ = v_code_4068_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                lean_inc(v___y_4044_);
                lean_inc_ref(v___y_4043_);
                lean_inc(v___y_4042_);
                lean_inc_ref(v___y_4041_);
                v___x_4048_ = lean_apply_6(
                    v_f_4040_,
                    v___y_4047_,
                    v___y_4041_,
                    v___y_4042_,
                    v___y_4043_,
                    v___y_4044_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_4048_) == 0 {
                    v_a_4049_ = lean_ctor_get(v___x_4048_, 0);
                    v_isSharedCheck_4057_ = (!lean_is_exclusive(v___x_4048_)) as u8;
                    if v_isSharedCheck_4057_ == 0 {
                        v___x_4051_ = v___x_4048_;
                        v_isShared_4052_ = v_isSharedCheck_4057_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4049_);
                        lean_dec(v___x_4048_);
                        v___x_4051_ = lean_box(0);
                        v_isShared_4052_ = v_isSharedCheck_4057_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_alt_4039_);
                    v_a_4058_ = lean_ctor_get(v___x_4048_, 0);
                    v_isSharedCheck_4065_ = (!lean_is_exclusive(v___x_4048_)) as u8;
                    if v_isSharedCheck_4065_ == 0 {
                        v___x_4060_ = v___x_4048_;
                        v_isShared_4061_ = v_isSharedCheck_4065_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4058_);
                        lean_dec(v___x_4048_);
                        v___x_4060_ = lean_box(0);
                        v_isShared_4061_ = v_isSharedCheck_4065_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4053_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_4039_, v_a_4049_);
                if v_isShared_4052_ == 0 {
                    lean_ctor_set(v___x_4051_, 0, v___x_4053_);
                    v___x_4055_ = v___x_4051_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4056_, 0, v___x_4053_);
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
                    v_reuseFailAlloc_4064_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_a_4058_);
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
    mut v_alt_4069_: *mut LeanObject,
    mut v_f_4070_: *mut LeanObject,
    mut v___y_4071_: *mut LeanObject,
    mut v___y_4072_: *mut LeanObject,
    mut v___y_4073_: *mut LeanObject,
    mut v___y_4074_: *mut LeanObject,
    mut v___y_4075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4076_: *mut LeanObject = core::ptr::null_mut();
    v_res_4076_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_alt_4069_, v_f_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
    lean_dec(v___y_4074_);
    lean_dec_ref(v___y_4073_);
    lean_dec(v___y_4072_);
    lean_dec_ref(v___y_4071_);
    return v_res_4076_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0(
    mut v_pu_4077_: u8,
    mut v_alt_4078_: *mut LeanObject,
    mut v_f_4079_: *mut LeanObject,
    mut v___y_4080_: *mut LeanObject,
    mut v___y_4081_: *mut LeanObject,
    mut v___y_4082_: *mut LeanObject,
    mut v___y_4083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    v___x_4085_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_alt_4078_, v_f_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_);
    return v___x_4085_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___boxed(
    mut v_pu_4086_: *mut LeanObject,
    mut v_alt_4087_: *mut LeanObject,
    mut v_f_4088_: *mut LeanObject,
    mut v___y_4089_: *mut LeanObject,
    mut v___y_4090_: *mut LeanObject,
    mut v___y_4091_: *mut LeanObject,
    mut v___y_4092_: *mut LeanObject,
    mut v___y_4093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4094_: u8 = 0;
    let mut v_res_4095_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4094_ = (lean_unbox(v_pu_4086_) as u8);
    v_res_4095_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0(v_pu_boxed_4094_, v_alt_4087_, v_f_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
    lean_dec(v___y_4092_);
    lean_dec_ref(v___y_4091_);
    lean_dec(v___y_4090_);
    lean_dec_ref(v___y_4089_);
    return v_res_4095_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0()
-> *mut LeanObject {
    let mut v___x_4096_: u8 = 0;
    let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
    v___x_4096_ = 1;
    v___x_4097_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_4096_);
    return v___x_4097_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(
    mut v_msg_4098_: *mut LeanObject,
    mut v___y_4099_: *mut LeanObject,
    mut v___y_4100_: *mut LeanObject,
    mut v___y_4101_: *mut LeanObject,
    mut v___y_4102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4109_: u8 = 0;
    let mut v_toFunctor_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4116_: u8 = 0;
    let mut v___f_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7095__overap_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4137_: u8 = 0;
    let mut v_unused_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4139_: u8 = 0;
    let mut v_unused_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4104_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0);
                v___x_4105_ = l_StateRefT_x27_instMonad___redArg(v___x_4104_);
                v_toApplicative_4106_ = lean_ctor_get(v___x_4105_, 0);
                v_isSharedCheck_4139_ = (!lean_is_exclusive(v___x_4105_)) as u8;
                if v_isSharedCheck_4139_ == 0 {
                    v_unused_4140_ = lean_ctor_get(v___x_4105_, 1);
                    lean_dec(v_unused_4140_);
                    v___x_4108_ = v___x_4105_;
                    v_isShared_4109_ = v_isSharedCheck_4139_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_4106_);
                    lean_dec(v___x_4105_);
                    v___x_4108_ = lean_box(0);
                    v_isShared_4109_ = v_isSharedCheck_4139_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_4110_ = lean_ctor_get(v_toApplicative_4106_, 0);
                v_toSeq_4111_ = lean_ctor_get(v_toApplicative_4106_, 2);
                v_toSeqLeft_4112_ = lean_ctor_get(v_toApplicative_4106_, 3);
                v_toSeqRight_4113_ = lean_ctor_get(v_toApplicative_4106_, 4);
                v_isSharedCheck_4137_ = (!lean_is_exclusive(v_toApplicative_4106_)) as u8;
                if v_isSharedCheck_4137_ == 0 {
                    v_unused_4138_ = lean_ctor_get(v_toApplicative_4106_, 1);
                    lean_dec(v_unused_4138_);
                    v___x_4115_ = v_toApplicative_4106_;
                    v_isShared_4116_ = v_isSharedCheck_4137_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_4113_);
                    lean_inc(v_toSeqLeft_4112_);
                    lean_inc(v_toSeq_4111_);
                    lean_inc(v_toFunctor_4110_);
                    lean_dec(v_toApplicative_4106_);
                    v___x_4115_ = lean_box(0);
                    v_isShared_4116_ = v_isSharedCheck_4137_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_4117_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1;
                v___f_4118_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2;
                lean_inc_ref(v_toFunctor_4110_);
                v___f_4119_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4119_, 0, v_toFunctor_4110_);
                v___f_4120_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4120_, 0, v_toFunctor_4110_);
                v___x_4121_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4121_, 0, v___f_4119_);
                lean_ctor_set(v___x_4121_, 1, v___f_4120_);
                v___f_4122_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4122_, 0, v_toSeqRight_4113_);
                v___f_4123_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4123_, 0, v_toSeqLeft_4112_);
                v___f_4124_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4124_, 0, v_toSeq_4111_);
                if v_isShared_4116_ == 0 {
                    lean_ctor_set(v___x_4115_, 4, v___f_4122_);
                    lean_ctor_set(v___x_4115_, 3, v___f_4123_);
                    lean_ctor_set(v___x_4115_, 2, v___f_4124_);
                    lean_ctor_set(v___x_4115_, 1, v___f_4117_);
                    lean_ctor_set(v___x_4115_, 0, v___x_4121_);
                    v___x_4126_ = v___x_4115_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4136_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4136_, 0, v___x_4121_);
                    lean_ctor_set(v_reuseFailAlloc_4136_, 1, v___f_4117_);
                    lean_ctor_set(v_reuseFailAlloc_4136_, 2, v___f_4124_);
                    lean_ctor_set(v_reuseFailAlloc_4136_, 3, v___f_4123_);
                    lean_ctor_set(v_reuseFailAlloc_4136_, 4, v___f_4122_);
                    v___x_4126_ = v_reuseFailAlloc_4136_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4109_ == 0 {
                    lean_ctor_set(v___x_4108_, 1, v___f_4118_);
                    lean_ctor_set(v___x_4108_, 0, v___x_4126_);
                    v___x_4128_ = v___x_4108_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4135_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4135_, 0, v___x_4126_);
                    lean_ctor_set(v_reuseFailAlloc_4135_, 1, v___f_4118_);
                    v___x_4128_ = v_reuseFailAlloc_4135_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4129_ = l_StateRefT_x27_instMonad___redArg(v___x_4128_);
                v___x_4130_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0);
                v___x_4131_ = l_instInhabitedOfMonad___redArg(v___x_4129_, v___x_4130_);
                v___f_4132_ = lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_4132_, 0, v___x_4131_);
                v___x_7095__overap_4133_ = lean_panic_fn_borrowed(v___f_4132_, v_msg_4098_);
                lean_dec_ref(v___f_4132_);
                lean_inc(v___y_4102_);
                lean_inc_ref(v___y_4101_);
                lean_inc(v___y_4100_);
                lean_inc_ref(v___y_4099_);
                v___x_4134_ = lean_apply_5(
                    v___x_7095__overap_4133_,
                    v___y_4099_,
                    v___y_4100_,
                    v___y_4101_,
                    v___y_4102_,
                    lean_box(0),
                );
                return v___x_4134_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___boxed(
    mut v_msg_4141_: *mut LeanObject,
    mut v___y_4142_: *mut LeanObject,
    mut v___y_4143_: *mut LeanObject,
    mut v___y_4144_: *mut LeanObject,
    mut v___y_4145_: *mut LeanObject,
    mut v___y_4146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4147_: *mut LeanObject = core::ptr::null_mut();
    v_res_4147_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(v_msg_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_);
    lean_dec(v___y_4145_);
    lean_dec_ref(v___y_4144_);
    lean_dec(v___y_4143_);
    lean_dec_ref(v___y_4142_);
    return v_res_4147_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4()
-> *mut LeanObject {
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    v___x_4154_ = lean_box(0);
    v___x_4155_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__3;
    v___x_4156_ = l_Lean_Expr_const___override(v___x_4155_, v___x_4154_);
    return v___x_4156_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0___boxed(
    mut v_resetTokenId_4157_: *mut LeanObject,
    mut v_origAllocId_4158_: *mut LeanObject,
    mut v_isSharedId_4159_: *mut LeanObject,
    mut v_resultType_4160_: *mut LeanObject,
    mut v_x_4161_: *mut LeanObject,
    mut v___y_4162_: *mut LeanObject,
    mut v___y_4163_: *mut LeanObject,
    mut v___y_4164_: *mut LeanObject,
    mut v___y_4165_: *mut LeanObject,
    mut v___y_4166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4167_: *mut LeanObject = core::ptr::null_mut();
    v_res_4167_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0(v_resetTokenId_4157_, v_origAllocId_4158_, v_isSharedId_4159_, v_resultType_4160_, v_x_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_);
    lean_dec(v___y_4165_);
    lean_dec_ref(v___y_4164_);
    lean_dec(v___y_4163_);
    lean_dec_ref(v___y_4162_);
    return v_res_4167_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(
    mut v_resetTokenId_4168_: *mut LeanObject,
    mut v_origAllocId_4169_: *mut LeanObject,
    mut v_isSharedId_4170_: *mut LeanObject,
    mut v_resultType_4171_: *mut LeanObject,
    mut v_i_4172_: *mut LeanObject,
    mut v_as_4173_: *mut LeanObject,
    mut v___y_4174_: *mut LeanObject,
    mut v___y_4175_: *mut LeanObject,
    mut v___y_4176_: *mut LeanObject,
    mut v___y_4177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: u8 = 0;
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: usize = 0;
    let mut v___x_4187_: usize = 0;
    let mut v___x_4188_: u8 = 0;
    let mut v___x_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4199_: u8 = 0;
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4203_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4179_ = lean_array_get_size(v_as_4173_);
                v___x_4180_ = lean_nat_dec_lt(v_i_4172_, v___x_4179_);
                if v___x_4180_ == 0 {
                    lean_dec(v_i_4172_);
                    lean_dec_ref(v_resultType_4171_);
                    lean_dec(v_isSharedId_4170_);
                    lean_dec(v_origAllocId_4169_);
                    lean_dec(v_resetTokenId_4168_);
                    v___x_4181_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4181_, 0, v_as_4173_);
                    return v___x_4181_;
                } else {
                    lean_inc_ref(v_resultType_4171_);
                    lean_inc(v_isSharedId_4170_);
                    lean_inc(v_origAllocId_4169_);
                    lean_inc(v_resetTokenId_4168_);
                    v___f_4182_ = lean_alloc_closure(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                    lean_closure_set(v___f_4182_, 0, v_resetTokenId_4168_);
                    lean_closure_set(v___f_4182_, 1, v_origAllocId_4169_);
                    lean_closure_set(v___f_4182_, 2, v_isSharedId_4170_);
                    lean_closure_set(v___f_4182_, 3, v_resultType_4171_);
                    v_a_4183_ = lean_array_fget_borrowed(v_as_4173_, v_i_4172_);
                    lean_inc(v_a_4183_);
                    v___x_4184_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_a_4183_, v___f_4182_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
                    if lean_obj_tag(v___x_4184_) == 0 {
                        v_a_4185_ = lean_ctor_get(v___x_4184_, 0);
                        lean_inc(v_a_4185_);
                        lean_dec_ref_known(v___x_4184_, 1);
                        v___x_4186_ = lean_ptr_addr(v_a_4183_);
                        v___x_4187_ = lean_ptr_addr(v_a_4185_);
                        v___x_4188_ = lean_usize_dec_eq(v___x_4186_, v___x_4187_);
                        if v___x_4188_ == 0 {
                            v___x_4189_ = lean_unsigned_to_nat(1);
                            v___x_4190_ = lean_nat_add(v_i_4172_, v___x_4189_);
                            v___x_4191_ = lean_array_fset(v_as_4173_, v_i_4172_, v_a_4185_);
                            lean_dec(v_i_4172_);
                            v_i_4172_ = v___x_4190_;
                            v_as_4173_ = v___x_4191_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_a_4185_);
                            v___x_4193_ = lean_unsigned_to_nat(1);
                            v___x_4194_ = lean_nat_add(v_i_4172_, v___x_4193_);
                            lean_dec(v_i_4172_);
                            v_i_4172_ = v___x_4194_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_as_4173_);
                        lean_dec(v_i_4172_);
                        lean_dec_ref(v_resultType_4171_);
                        lean_dec(v_isSharedId_4170_);
                        lean_dec(v_origAllocId_4169_);
                        lean_dec(v_resetTokenId_4168_);
                        v_a_4196_ = lean_ctor_get(v___x_4184_, 0);
                        v_isSharedCheck_4203_ = (!lean_is_exclusive(v___x_4184_)) as u8;
                        if v_isSharedCheck_4203_ == 0 {
                            v___x_4198_ = v___x_4184_;
                            v_isShared_4199_ = v_isSharedCheck_4203_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4196_);
                            lean_dec(v___x_4184_);
                            v___x_4198_ = lean_box(0);
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
                    v_reuseFailAlloc_4202_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_a_4196_);
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
-> *mut LeanObject {
    let mut v___x_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    v___x_4206_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__6;
    v___x_4207_ = lean_unsigned_to_nat(6);
    v___x_4208_ = lean_unsigned_to_nat(208);
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
    mut v_resetTokenId_4212_: *mut LeanObject,
    mut v_code_4213_: *mut LeanObject,
    mut v_origAllocId_4214_: *mut LeanObject,
    mut v_isSharedId_4215_: *mut LeanObject,
    mut v_currentRetType_4216_: *mut LeanObject,
    mut v_a_4217_: *mut LeanObject,
    mut v_a_4218_: *mut LeanObject,
    mut v_a_4219_: *mut LeanObject,
    mut v_a_4220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decl_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_updateHeader_4230_: u8 = 0;
    let mut v_args_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4234_: u8 = 0;
    let mut v___x_4235_: u8 = 0;
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4240_: u8 = 0;
    let mut v___x_4241_: usize = 0;
    let mut v___x_4242_: usize = 0;
    let mut v___x_4243_: u8 = 0;
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4246_: u8 = 0;
    let mut v___x_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4253_: u8 = 0;
    let mut v_unused_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4259_: u8 = 0;
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4262_: u8 = 0;
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: u8 = 0;
    let mut v___x_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: u8 = 0;
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4295_: u8 = 0;
    let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4302_: u8 = 0;
    let mut v_a_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4306_: u8 = 0;
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4310_: u8 = 0;
    let mut v_a_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4314_: u8 = 0;
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4318_: u8 = 0;
    let mut v_reuseFailAlloc_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4323_: u8 = 0;
    let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4327_: u8 = 0;
    let mut v_a_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4331_: u8 = 0;
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4335_: u8 = 0;
    let mut v_a_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4339_: u8 = 0;
    let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4343_: u8 = 0;
    let mut v_isSharedCheck_4344_: u8 = 0;
    let mut v_unused_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4347_: u8 = 0;
    let mut v_k_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4353_: u8 = 0;
    let mut v___x_4354_: usize = 0;
    let mut v___x_4355_: usize = 0;
    let mut v___x_4356_: u8 = 0;
    let mut v___x_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4359_: u8 = 0;
    let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4366_: u8 = 0;
    let mut v_unused_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4372_: u8 = 0;
    let mut v_decl_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: u8 = 0;
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4387_: u8 = 0;
    let mut v___y_4389_: u8 = 0;
    let mut v___x_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4392_: u8 = 0;
    let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4399_: u8 = 0;
    let mut v_unused_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: usize = 0;
    let mut v___x_4406_: usize = 0;
    let mut v___x_4407_: u8 = 0;
    let mut v___x_4408_: usize = 0;
    let mut v___x_4409_: usize = 0;
    let mut v___x_4410_: u8 = 0;
    let mut v_isSharedCheck_4411_: u8 = 0;
    let mut v_a_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4415_: u8 = 0;
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4419_: u8 = 0;
    let mut v_cases_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_resultType_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discr_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4427_: u8 = 0;
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4433_: u8 = 0;
    let mut v___x_4434_: usize = 0;
    let mut v___x_4435_: usize = 0;
    let mut v___x_4436_: u8 = 0;
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4439_: u8 = 0;
    let mut v___x_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4449_: u8 = 0;
    let mut v_unused_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4454_: u8 = 0;
    let mut v_a_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4458_: u8 = 0;
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4462_: u8 = 0;
    let mut v_isSharedCheck_4463_: u8 = 0;
    let mut v_fvarId_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4472_: u8 = 0;
    let mut v___x_4473_: usize = 0;
    let mut v___x_4474_: usize = 0;
    let mut v___x_4475_: u8 = 0;
    let mut v___x_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4478_: u8 = 0;
    let mut v___x_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4485_: u8 = 0;
    let mut v_unused_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4493_: u8 = 0;
    let mut v_fvarId_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4502_: u8 = 0;
    let mut v___x_4503_: usize = 0;
    let mut v___x_4504_: usize = 0;
    let mut v___x_4505_: u8 = 0;
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4508_: u8 = 0;
    let mut v___x_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4515_: u8 = 0;
    let mut v_unused_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4523_: u8 = 0;
    let mut v_fvarId_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4534_: u8 = 0;
    let mut v___x_4535_: usize = 0;
    let mut v___x_4536_: usize = 0;
    let mut v___x_4537_: u8 = 0;
    let mut v___x_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4540_: u8 = 0;
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4547_: u8 = 0;
    let mut v_unused_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4557_: u8 = 0;
    let mut v_fvarId_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cidx_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4565_: u8 = 0;
    let mut v___x_4566_: usize = 0;
    let mut v___x_4567_: usize = 0;
    let mut v___x_4568_: u8 = 0;
    let mut v___x_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4571_: u8 = 0;
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4578_: u8 = 0;
    let mut v_unused_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4585_: u8 = 0;
    let mut v_fvarId_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_check_4588_: u8 = 0;
    let mut v_persistent_4589_: u8 = 0;
    let mut v_k_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4595_: u8 = 0;
    let mut v___x_4596_: usize = 0;
    let mut v___x_4597_: usize = 0;
    let mut v___x_4598_: u8 = 0;
    let mut v___x_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4601_: u8 = 0;
    let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4608_: u8 = 0;
    let mut v_unused_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4615_: u8 = 0;
    let mut v_fvarId_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_check_4618_: u8 = 0;
    let mut v_persistent_4619_: u8 = 0;
    let mut v_objs_x3f_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: u8 = 0;
    let mut v___x_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4627_: u8 = 0;
    let mut v___x_4628_: usize = 0;
    let mut v___x_4629_: usize = 0;
    let mut v___x_4630_: u8 = 0;
    let mut v___x_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4633_: u8 = 0;
    let mut v___x_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4640_: u8 = 0;
    let mut v_unused_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4648_: u8 = 0;
    let mut v___x_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: u8 = 0;
    let mut v___x_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4661_: u8 = 0;
    let mut v___x_4662_: usize = 0;
    let mut v___x_4663_: usize = 0;
    let mut v___x_4664_: u8 = 0;
    let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4667_: u8 = 0;
    let mut v___x_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4674_: u8 = 0;
    let mut v_unused_4675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4680_: u8 = 0;
    let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_code_4213_) {
                0 => {
                    v_decl_4222_ = lean_ctor_get(v_code_4213_, 0);
                    v_value_4223_ = lean_ctor_get(v_decl_4222_, 3);
                    lean_inc(v_value_4223_);
                    if lean_obj_tag(v_value_4223_) == 12 {
                        v_k_4224_ = lean_ctor_get(v_code_4213_, 1);
                        v_fvarId_4225_ = lean_ctor_get(v_decl_4222_, 0);
                        v_binderName_4226_ = lean_ctor_get(v_decl_4222_, 1);
                        v_type_4227_ = lean_ctor_get(v_decl_4222_, 2);
                        v_var_4228_ = lean_ctor_get(v_value_4223_, 0);
                        v_i_4229_ = lean_ctor_get(v_value_4223_, 1);
                        v_updateHeader_4230_ = lean_ctor_get_uint8(
                            v_value_4223_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        );
                        v_args_4231_ = lean_ctor_get(v_value_4223_, 2);
                        v_isSharedCheck_4347_ = (!lean_is_exclusive(v_value_4223_)) as u8;
                        if v_isSharedCheck_4347_ == 0 {
                            v___x_4233_ = v_value_4223_;
                            v_isShared_4234_ = v_isSharedCheck_4347_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_args_4231_);
                            lean_inc(v_i_4229_);
                            lean_inc(v_var_4228_);
                            lean_dec(v_value_4223_);
                            v___x_4233_ = lean_box(0);
                            v_isShared_4234_ = v_isSharedCheck_4347_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_value_4223_);
                        v_k_4348_ = lean_ctor_get(v_code_4213_, 1);
                        lean_inc_ref(v_k_4348_);
                        v___x_4349_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_4212_, v_k_4348_, v_origAllocId_4214_, v_isSharedId_4215_, v_currentRetType_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                        if lean_obj_tag(v___x_4349_) == 0 {
                            v_a_4350_ = lean_ctor_get(v___x_4349_, 0);
                            v_isSharedCheck_4372_ = (!lean_is_exclusive(v___x_4349_)) as u8;
                            if v_isSharedCheck_4372_ == 0 {
                                v___x_4352_ = v___x_4349_;
                                v_isShared_4353_ = v_isSharedCheck_4372_;
                                state = 22;
                                continue;
                            } else {
                                lean_inc(v_a_4350_);
                                lean_dec(v___x_4349_);
                                v___x_4352_ = lean_box(0);
                                v_isShared_4353_ = v_isSharedCheck_4372_;
                                state = 22;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_code_4213_, 2);
                            return v___x_4349_;
                        }
                    }
                }
                2 => {
                    v_decl_4373_ = lean_ctor_get(v_code_4213_, 0);
                    v_k_4374_ = lean_ctor_get(v_code_4213_, 1);
                    v_params_4375_ = lean_ctor_get(v_decl_4373_, 2);
                    v_type_4376_ = lean_ctor_get(v_decl_4373_, 3);
                    v_value_4377_ = lean_ctor_get(v_decl_4373_, 4);
                    lean_inc_ref(v_type_4376_);
                    lean_inc(v_isSharedId_4215_);
                    lean_inc(v_origAllocId_4214_);
                    lean_inc_ref(v_value_4377_);
                    lean_inc(v_resetTokenId_4212_);
                    v___x_4378_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_4212_, v_value_4377_, v_origAllocId_4214_, v_isSharedId_4215_, v_type_4376_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    if lean_obj_tag(v___x_4378_) == 0 {
                        v_a_4379_ = lean_ctor_get(v___x_4378_, 0);
                        lean_inc(v_a_4379_);
                        lean_dec_ref_known(v___x_4378_, 1);
                        v___x_4380_ = 1;
                        lean_inc_ref(v_params_4375_);
                        lean_inc_ref(v_type_4376_);
                        lean_inc_ref(v_decl_4373_);
                        v___x_4381_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_4380_, v_decl_4373_, v_type_4376_, v_params_4375_, v_a_4379_, v_a_4218_);
                        if lean_obj_tag(v___x_4381_) == 0 {
                            v_a_4382_ = lean_ctor_get(v___x_4381_, 0);
                            lean_inc(v_a_4382_);
                            lean_dec_ref_known(v___x_4381_, 1);
                            lean_inc_ref(v_k_4374_);
                            v___x_4383_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_4212_, v_k_4374_, v_origAllocId_4214_, v_isSharedId_4215_, v_currentRetType_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                            if lean_obj_tag(v___x_4383_) == 0 {
                                v_a_4384_ = lean_ctor_get(v___x_4383_, 0);
                                v_isSharedCheck_4411_ = (!lean_is_exclusive(v___x_4383_)) as u8;
                                if v_isSharedCheck_4411_ == 0 {
                                    v___x_4386_ = v___x_4383_;
                                    v_isShared_4387_ = v_isSharedCheck_4411_;
                                    state = 27;
                                    continue;
                                } else {
                                    lean_inc(v_a_4384_);
                                    lean_dec(v___x_4383_);
                                    v___x_4386_ = lean_box(0);
                                    v_isShared_4387_ = v_isSharedCheck_4411_;
                                    state = 27;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_4382_);
                                lean_dec_ref_known(v_code_4213_, 2);
                                return v___x_4383_;
                            }
                        } else {
                            lean_dec_ref_known(v_code_4213_, 2);
                            lean_dec_ref(v_currentRetType_4216_);
                            lean_dec(v_isSharedId_4215_);
                            lean_dec(v_origAllocId_4214_);
                            lean_dec(v_resetTokenId_4212_);
                            v_a_4412_ = lean_ctor_get(v___x_4381_, 0);
                            v_isSharedCheck_4419_ = (!lean_is_exclusive(v___x_4381_)) as u8;
                            if v_isSharedCheck_4419_ == 0 {
                                v___x_4414_ = v___x_4381_;
                                v_isShared_4415_ = v_isSharedCheck_4419_;
                                state = 33;
                                continue;
                            } else {
                                lean_inc(v_a_4412_);
                                lean_dec(v___x_4381_);
                                v___x_4414_ = lean_box(0);
                                v_isShared_4415_ = v_isSharedCheck_4419_;
                                state = 33;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_code_4213_, 2);
                        lean_dec_ref(v_currentRetType_4216_);
                        lean_dec(v_isSharedId_4215_);
                        lean_dec(v_origAllocId_4214_);
                        lean_dec(v_resetTokenId_4212_);
                        return v___x_4378_;
                    }
                }
                4 => {
                    lean_dec_ref(v_currentRetType_4216_);
                    v_cases_4420_ = lean_ctor_get(v_code_4213_, 0);
                    lean_inc_ref(v_cases_4420_);
                    v_typeName_4421_ = lean_ctor_get(v_cases_4420_, 0);
                    v_resultType_4422_ = lean_ctor_get(v_cases_4420_, 1);
                    v_discr_4423_ = lean_ctor_get(v_cases_4420_, 2);
                    v_alts_4424_ = lean_ctor_get(v_cases_4420_, 3);
                    v_isSharedCheck_4463_ = (!lean_is_exclusive(v_cases_4420_)) as u8;
                    if v_isSharedCheck_4463_ == 0 {
                        v___x_4426_ = v_cases_4420_;
                        v_isShared_4427_ = v_isSharedCheck_4463_;
                        state = 35;
                        continue;
                    } else {
                        lean_inc(v_alts_4424_);
                        lean_inc(v_discr_4423_);
                        lean_inc(v_resultType_4422_);
                        lean_inc(v_typeName_4421_);
                        lean_dec(v_cases_4420_);
                        v___x_4426_ = lean_box(0);
                        v_isShared_4427_ = v_isSharedCheck_4463_;
                        state = 35;
                        continue;
                    }
                }
                7 => {
                    v_fvarId_4464_ = lean_ctor_get(v_code_4213_, 0);
                    v_i_4465_ = lean_ctor_get(v_code_4213_, 1);
                    v_y_4466_ = lean_ctor_get(v_code_4213_, 2);
                    v_k_4467_ = lean_ctor_get(v_code_4213_, 3);
                    lean_inc_ref(v_k_4467_);
                    v___x_4468_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_4212_, v_k_4467_, v_origAllocId_4214_, v_isSharedId_4215_, v_currentRetType_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    if lean_obj_tag(v___x_4468_) == 0 {
                        v_a_4469_ = lean_ctor_get(v___x_4468_, 0);
                        v_isSharedCheck_4493_ = (!lean_is_exclusive(v___x_4468_)) as u8;
                        if v_isSharedCheck_4493_ == 0 {
                            v___x_4471_ = v___x_4468_;
                            v_isShared_4472_ = v_isSharedCheck_4493_;
                            state = 44;
                            continue;
                        } else {
                            lean_inc(v_a_4469_);
                            lean_dec(v___x_4468_);
                            v___x_4471_ = lean_box(0);
                            v_isShared_4472_ = v_isSharedCheck_4493_;
                            state = 44;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_code_4213_, 4);
                        return v___x_4468_;
                    }
                }
                8 => {
                    v_fvarId_4494_ = lean_ctor_get(v_code_4213_, 0);
                    v_i_4495_ = lean_ctor_get(v_code_4213_, 1);
                    v_y_4496_ = lean_ctor_get(v_code_4213_, 2);
                    v_k_4497_ = lean_ctor_get(v_code_4213_, 3);
                    lean_inc_ref(v_k_4497_);
                    v___x_4498_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_4212_, v_k_4497_, v_origAllocId_4214_, v_isSharedId_4215_, v_currentRetType_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    if lean_obj_tag(v___x_4498_) == 0 {
                        v_a_4499_ = lean_ctor_get(v___x_4498_, 0);
                        v_isSharedCheck_4523_ = (!lean_is_exclusive(v___x_4498_)) as u8;
                        if v_isSharedCheck_4523_ == 0 {
                            v___x_4501_ = v___x_4498_;
                            v_isShared_4502_ = v_isSharedCheck_4523_;
                            state = 49;
                            continue;
                        } else {
                            lean_inc(v_a_4499_);
                            lean_dec(v___x_4498_);
                            v___x_4501_ = lean_box(0);
                            v_isShared_4502_ = v_isSharedCheck_4523_;
                            state = 49;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_code_4213_, 4);
                        return v___x_4498_;
                    }
                }
                9 => {
                    v_fvarId_4524_ = lean_ctor_get(v_code_4213_, 0);
                    v_i_4525_ = lean_ctor_get(v_code_4213_, 1);
                    v_offset_4526_ = lean_ctor_get(v_code_4213_, 2);
                    v_y_4527_ = lean_ctor_get(v_code_4213_, 3);
                    v_ty_4528_ = lean_ctor_get(v_code_4213_, 4);
                    v_k_4529_ = lean_ctor_get(v_code_4213_, 5);
                    lean_inc_ref(v_k_4529_);
                    v___x_4530_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_4212_, v_k_4529_, v_origAllocId_4214_, v_isSharedId_4215_, v_currentRetType_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    if lean_obj_tag(v___x_4530_) == 0 {
                        v_a_4531_ = lean_ctor_get(v___x_4530_, 0);
                        v_isSharedCheck_4557_ = (!lean_is_exclusive(v___x_4530_)) as u8;
                        if v_isSharedCheck_4557_ == 0 {
                            v___x_4533_ = v___x_4530_;
                            v_isShared_4534_ = v_isSharedCheck_4557_;
                            state = 54;
                            continue;
                        } else {
                            lean_inc(v_a_4531_);
                            lean_dec(v___x_4530_);
                            v___x_4533_ = lean_box(0);
                            v_isShared_4534_ = v_isSharedCheck_4557_;
                            state = 54;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_code_4213_, 6);
                        return v___x_4530_;
                    }
                }
                10 => {
                    v_fvarId_4558_ = lean_ctor_get(v_code_4213_, 0);
                    v_cidx_4559_ = lean_ctor_get(v_code_4213_, 1);
                    v_k_4560_ = lean_ctor_get(v_code_4213_, 2);
                    lean_inc_ref(v_k_4560_);
                    v___x_4561_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_4212_, v_k_4560_, v_origAllocId_4214_, v_isSharedId_4215_, v_currentRetType_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    if lean_obj_tag(v___x_4561_) == 0 {
                        v_a_4562_ = lean_ctor_get(v___x_4561_, 0);
                        v_isSharedCheck_4585_ = (!lean_is_exclusive(v___x_4561_)) as u8;
                        if v_isSharedCheck_4585_ == 0 {
                            v___x_4564_ = v___x_4561_;
                            v_isShared_4565_ = v_isSharedCheck_4585_;
                            state = 59;
                            continue;
                        } else {
                            lean_inc(v_a_4562_);
                            lean_dec(v___x_4561_);
                            v___x_4564_ = lean_box(0);
                            v_isShared_4565_ = v_isSharedCheck_4585_;
                            state = 59;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_code_4213_, 3);
                        return v___x_4561_;
                    }
                }
                11 => {
                    v_fvarId_4586_ = lean_ctor_get(v_code_4213_, 0);
                    v_n_4587_ = lean_ctor_get(v_code_4213_, 1);
                    v_check_4588_ = lean_ctor_get_uint8(
                        v_code_4213_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_persistent_4589_ = lean_ctor_get_uint8(
                        v_code_4213_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_k_4590_ = lean_ctor_get(v_code_4213_, 2);
                    lean_inc_ref(v_k_4590_);
                    v___x_4591_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_4212_, v_k_4590_, v_origAllocId_4214_, v_isSharedId_4215_, v_currentRetType_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    if lean_obj_tag(v___x_4591_) == 0 {
                        v_a_4592_ = lean_ctor_get(v___x_4591_, 0);
                        v_isSharedCheck_4615_ = (!lean_is_exclusive(v___x_4591_)) as u8;
                        if v_isSharedCheck_4615_ == 0 {
                            v___x_4594_ = v___x_4591_;
                            v_isShared_4595_ = v_isSharedCheck_4615_;
                            state = 64;
                            continue;
                        } else {
                            lean_inc(v_a_4592_);
                            lean_dec(v___x_4591_);
                            v___x_4594_ = lean_box(0);
                            v_isShared_4595_ = v_isSharedCheck_4615_;
                            state = 64;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_code_4213_, 3);
                        return v___x_4591_;
                    }
                }
                12 => {
                    v_fvarId_4616_ = lean_ctor_get(v_code_4213_, 0);
                    v_n_4617_ = lean_ctor_get(v_code_4213_, 1);
                    v_check_4618_ = lean_ctor_get_uint8(
                        v_code_4213_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    );
                    v_persistent_4619_ = lean_ctor_get_uint8(
                        v_code_4213_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                    );
                    v_objs_x3f_4620_ = lean_ctor_get(v_code_4213_, 2);
                    v_k_4621_ = lean_ctor_get(v_code_4213_, 3);
                    v___x_4622_ = l_Lean_instBEqFVarId_beq(v_resetTokenId_4212_, v_fvarId_4616_);
                    if v___x_4622_ == 0 {
                        lean_inc_ref(v_k_4621_);
                        v___x_4623_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_4212_, v_k_4621_, v_origAllocId_4214_, v_isSharedId_4215_, v_currentRetType_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                        if lean_obj_tag(v___x_4623_) == 0 {
                            v_a_4624_ = lean_ctor_get(v___x_4623_, 0);
                            v_isSharedCheck_4648_ = (!lean_is_exclusive(v___x_4623_)) as u8;
                            if v_isSharedCheck_4648_ == 0 {
                                v___x_4626_ = v___x_4623_;
                                v_isShared_4627_ = v_isSharedCheck_4648_;
                                state = 69;
                                continue;
                            } else {
                                lean_inc(v_a_4624_);
                                lean_dec(v___x_4623_);
                                v___x_4626_ = lean_box(0);
                                v_isShared_4627_ = v_isSharedCheck_4648_;
                                state = 69;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_code_4213_, 4);
                            return v___x_4623_;
                        }
                    } else {
                        lean_inc_ref(v_k_4621_);
                        lean_inc(v_n_4617_);
                        lean_dec_ref_known(v_code_4213_, 4);
                        lean_dec_ref(v_currentRetType_4216_);
                        lean_dec(v_isSharedId_4215_);
                        lean_dec(v_origAllocId_4214_);
                        v___x_4649_ = lean_unsigned_to_nat(1);
                        v___x_4650_ = lean_nat_dec_eq(v_n_4617_, v___x_4649_);
                        lean_dec(v_n_4617_);
                        if v___x_4650_ == 0 {
                            lean_dec_ref(v_k_4621_);
                            lean_dec(v_resetTokenId_4212_);
                            v___x_4651_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7_once), _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7);
                            v___x_4652_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(v___x_4651_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                            return v___x_4652_;
                        } else {
                            v___x_4653_ = lean_alloc_ctor(13, 2, (0) as u32);
                            lean_ctor_set(v___x_4653_, 0, v_resetTokenId_4212_);
                            lean_ctor_set(v___x_4653_, 1, v_k_4621_);
                            v___x_4654_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_4654_, 0, v___x_4653_);
                            return v___x_4654_;
                        }
                    }
                }
                13 => {
                    v_fvarId_4655_ = lean_ctor_get(v_code_4213_, 0);
                    v_k_4656_ = lean_ctor_get(v_code_4213_, 1);
                    lean_inc_ref(v_k_4656_);
                    v___x_4657_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_4212_, v_k_4656_, v_origAllocId_4214_, v_isSharedId_4215_, v_currentRetType_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    if lean_obj_tag(v___x_4657_) == 0 {
                        v_a_4658_ = lean_ctor_get(v___x_4657_, 0);
                        v_isSharedCheck_4680_ = (!lean_is_exclusive(v___x_4657_)) as u8;
                        if v_isSharedCheck_4680_ == 0 {
                            v___x_4660_ = v___x_4657_;
                            v_isShared_4661_ = v_isSharedCheck_4680_;
                            state = 74;
                            continue;
                        } else {
                            lean_inc(v_a_4658_);
                            lean_dec(v___x_4657_);
                            v___x_4660_ = lean_box(0);
                            v_isShared_4661_ = v_isSharedCheck_4680_;
                            state = 74;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_code_4213_, 2);
                        return v___x_4657_;
                    }
                }
                _ => {
                    lean_dec_ref(v_currentRetType_4216_);
                    lean_dec(v_isSharedId_4215_);
                    lean_dec(v_origAllocId_4214_);
                    lean_dec(v_resetTokenId_4212_);
                    v___x_4681_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4681_, 0, v_code_4213_);
                    return v___x_4681_;
                }
            },
            1 => {
                v___x_4235_ = l_Lean_instBEqFVarId_beq(v_resetTokenId_4212_, v_var_4228_);
                lean_dec(v_var_4228_);
                if v___x_4235_ == 0 {
                    lean_del_object(v___x_4233_);
                    lean_dec_ref(v_args_4231_);
                    lean_dec_ref(v_i_4229_);
                    lean_inc_ref(v_k_4224_);
                    v___x_4236_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_4212_, v_k_4224_, v_origAllocId_4214_, v_isSharedId_4215_, v_currentRetType_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    if lean_obj_tag(v___x_4236_) == 0 {
                        v_a_4237_ = lean_ctor_get(v___x_4236_, 0);
                        v_isSharedCheck_4259_ = (!lean_is_exclusive(v___x_4236_)) as u8;
                        if v_isSharedCheck_4259_ == 0 {
                            v___x_4239_ = v___x_4236_;
                            v_isShared_4240_ = v_isSharedCheck_4259_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_4237_);
                            lean_dec(v___x_4236_);
                            v___x_4239_ = lean_box(0);
                            v_isShared_4240_ = v_isSharedCheck_4259_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_code_4213_, 2);
                        return v___x_4236_;
                    }
                } else {
                    lean_inc_ref(v_k_4224_);
                    lean_inc_ref(v_decl_4222_);
                    v_isSharedCheck_4344_ = (!lean_is_exclusive(v_code_4213_)) as u8;
                    if v_isSharedCheck_4344_ == 0 {
                        v_unused_4345_ = lean_ctor_get(v_code_4213_, 1);
                        lean_dec(v_unused_4345_);
                        v_unused_4346_ = lean_ctor_get(v_code_4213_, 0);
                        lean_dec(v_unused_4346_);
                        v___x_4261_ = v_code_4213_;
                        v_isShared_4262_ = v_isSharedCheck_4344_;
                        state = 7;
                        continue;
                    } else {
                        lean_dec(v_code_4213_);
                        v___x_4261_ = lean_box(0);
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
                    lean_inc_ref(v_decl_4222_);
                    v_isSharedCheck_4253_ = (!lean_is_exclusive(v_code_4213_)) as u8;
                    if v_isSharedCheck_4253_ == 0 {
                        v_unused_4254_ = lean_ctor_get(v_code_4213_, 1);
                        lean_dec(v_unused_4254_);
                        v_unused_4255_ = lean_ctor_get(v_code_4213_, 0);
                        lean_dec(v_unused_4255_);
                        v___x_4245_ = v_code_4213_;
                        v_isShared_4246_ = v_isSharedCheck_4253_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_code_4213_);
                        v___x_4245_ = lean_box(0);
                        v_isShared_4246_ = v_isSharedCheck_4253_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4237_);
                    if v_isShared_4240_ == 0 {
                        lean_ctor_set(v___x_4239_, 0, v_code_4213_);
                        v___x_4257_ = v___x_4239_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4258_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_code_4213_);
                        v___x_4257_ = v_reuseFailAlloc_4258_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4246_ == 0 {
                    lean_ctor_set(v___x_4245_, 1, v_a_4237_);
                    v___x_4248_ = v___x_4245_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4252_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_decl_4222_);
                    lean_ctor_set(v_reuseFailAlloc_4252_, 1, v_a_4237_);
                    v___x_4248_ = v_reuseFailAlloc_4252_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4240_ == 0 {
                    lean_ctor_set(v___x_4239_, 0, v___x_4248_);
                    v___x_4250_ = v___x_4239_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4251_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4251_, 0, v___x_4248_);
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
                if lean_obj_tag(v___x_4263_) == 0 {
                    v_a_4264_ = lean_ctor_get(v___x_4263_, 0);
                    lean_inc(v_a_4264_);
                    lean_dec_ref_known(v___x_4263_, 1);
                    v_fst_4265_ = lean_ctor_get(v_a_4264_, 0);
                    lean_inc(v_fst_4265_);
                    v_snd_4266_ = lean_ctor_get(v_a_4264_, 1);
                    lean_inc(v_snd_4266_);
                    lean_dec(v_a_4264_);
                    v___x_4267_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(v_origAllocId_4214_, v_fst_4265_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    lean_dec(v_fst_4265_);
                    if lean_obj_tag(v___x_4267_) == 0 {
                        v_a_4268_ = lean_ctor_get(v___x_4267_, 0);
                        lean_inc(v_a_4268_);
                        lean_dec_ref_known(v___x_4267_, 1);
                        v_fst_4269_ = lean_ctor_get(v_a_4268_, 0);
                        lean_inc(v_fst_4269_);
                        v_snd_4270_ = lean_ctor_get(v_a_4268_, 1);
                        lean_inc(v_snd_4270_);
                        lean_dec(v_a_4268_);
                        v___x_4271_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__1;
                        v___x_4272_ =
                            l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4271_, v_a_4218_);
                        if lean_obj_tag(v___x_4272_) == 0 {
                            v_a_4273_ = lean_ctor_get(v___x_4272_, 0);
                            lean_inc(v_a_4273_);
                            lean_dec_ref_known(v___x_4272_, 1);
                            v___x_4274_ = 1;
                            v___x_4275_ = l_Lean_Compiler_LCNF_attachCodeDecls(
                                v___x_4274_,
                                v_snd_4270_,
                                v_snd_4266_,
                            );
                            lean_dec(v_snd_4270_);
                            v___x_4276_ = 0;
                            lean_inc_ref(v_type_4227_);
                            lean_inc(v_binderName_4226_);
                            lean_inc(v_fvarId_4225_);
                            if v_isShared_4234_ == 0 {
                                lean_ctor_set_tag(v___x_4233_, 0);
                                lean_ctor_set(v___x_4233_, 2, v_type_4227_);
                                lean_ctor_set(v___x_4233_, 1, v_binderName_4226_);
                                lean_ctor_set(v___x_4233_, 0, v_fvarId_4225_);
                                v___x_4278_ = v___x_4233_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_4319_ = lean_alloc_ctor(0, 3, (1) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_fvarId_4225_);
                                lean_ctor_set(v_reuseFailAlloc_4319_, 1, v_binderName_4226_);
                                lean_ctor_set(v_reuseFailAlloc_4319_, 2, v_type_4227_);
                                v___x_4278_ = v_reuseFailAlloc_4319_;
                                state = 8;
                                continue;
                            }
                        } else {
                            lean_dec(v_snd_4270_);
                            lean_dec(v_fst_4269_);
                            lean_dec(v_snd_4266_);
                            lean_del_object(v___x_4261_);
                            lean_del_object(v___x_4233_);
                            lean_dec_ref(v_args_4231_);
                            lean_dec_ref(v_i_4229_);
                            lean_dec_ref(v_decl_4222_);
                            lean_dec_ref(v_currentRetType_4216_);
                            lean_dec(v_isSharedId_4215_);
                            lean_dec(v_origAllocId_4214_);
                            lean_dec(v_resetTokenId_4212_);
                            v_a_4320_ = lean_ctor_get(v___x_4272_, 0);
                            v_isSharedCheck_4327_ = (!lean_is_exclusive(v___x_4272_)) as u8;
                            if v_isSharedCheck_4327_ == 0 {
                                v___x_4322_ = v___x_4272_;
                                v_isShared_4323_ = v_isSharedCheck_4327_;
                                state = 16;
                                continue;
                            } else {
                                lean_inc(v_a_4320_);
                                lean_dec(v___x_4272_);
                                v___x_4322_ = lean_box(0);
                                v_isShared_4323_ = v_isSharedCheck_4327_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_snd_4266_);
                        lean_del_object(v___x_4261_);
                        lean_del_object(v___x_4233_);
                        lean_dec_ref(v_args_4231_);
                        lean_dec_ref(v_i_4229_);
                        lean_dec_ref(v_decl_4222_);
                        lean_dec_ref(v_currentRetType_4216_);
                        lean_dec(v_isSharedId_4215_);
                        lean_dec(v_origAllocId_4214_);
                        lean_dec(v_resetTokenId_4212_);
                        v_a_4328_ = lean_ctor_get(v___x_4267_, 0);
                        v_isSharedCheck_4335_ = (!lean_is_exclusive(v___x_4267_)) as u8;
                        if v_isSharedCheck_4335_ == 0 {
                            v___x_4330_ = v___x_4267_;
                            v_isShared_4331_ = v_isSharedCheck_4335_;
                            state = 18;
                            continue;
                        } else {
                            lean_inc(v_a_4328_);
                            lean_dec(v___x_4267_);
                            v___x_4330_ = lean_box(0);
                            v_isShared_4331_ = v_isSharedCheck_4335_;
                            state = 18;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4261_);
                    lean_del_object(v___x_4233_);
                    lean_dec_ref(v_args_4231_);
                    lean_dec_ref(v_i_4229_);
                    lean_dec_ref(v_decl_4222_);
                    lean_dec_ref(v_currentRetType_4216_);
                    lean_dec(v_isSharedId_4215_);
                    lean_dec(v_origAllocId_4214_);
                    lean_dec(v_resetTokenId_4212_);
                    v_a_4336_ = lean_ctor_get(v___x_4263_, 0);
                    v_isSharedCheck_4343_ = (!lean_is_exclusive(v___x_4263_)) as u8;
                    if v_isSharedCheck_4343_ == 0 {
                        v___x_4338_ = v___x_4263_;
                        v_isShared_4339_ = v_isSharedCheck_4343_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_a_4336_);
                        lean_dec(v___x_4263_);
                        v___x_4338_ = lean_box(0);
                        v_isShared_4339_ = v_isSharedCheck_4343_;
                        state = 20;
                        continue;
                    }
                }
            }
            8 => {
                lean_ctor_set_uint8(
                    v___x_4278_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_4276_,
                );
                v___x_4279_ = lean_unsigned_to_nat(1);
                v___x_4280_ = lean_mk_empty_array_with_capacity(v___x_4279_);
                v___x_4281_ = lean_array_push(v___x_4280_, v___x_4278_);
                lean_inc_ref(v_currentRetType_4216_);
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
                if lean_obj_tag(v___x_4282_) == 0 {
                    v_a_4283_ = lean_ctor_get(v___x_4282_, 0);
                    lean_inc(v_a_4283_);
                    lean_dec_ref_known(v___x_4282_, 1);
                    v_fvarId_4284_ = lean_ctor_get(v_a_4283_, 0);
                    lean_inc(v_fvarId_4284_);
                    lean_inc_ref(v_args_4231_);
                    lean_inc_ref(v_i_4229_);
                    lean_inc_ref(v_decl_4222_);
                    v___x_4285_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(v_decl_4222_, v_i_4229_, v_args_4231_, v_fvarId_4284_, v_fst_4269_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    if lean_obj_tag(v___x_4285_) == 0 {
                        v_a_4286_ = lean_ctor_get(v___x_4285_, 0);
                        lean_inc(v_a_4286_);
                        lean_dec_ref_known(v___x_4285_, 1);
                        lean_inc(v_fvarId_4284_);
                        v___x_4287_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(v_resetTokenId_4212_, v_i_4229_, v_updateHeader_4230_, v_args_4231_, v_fvarId_4284_, v_origAllocId_4214_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                        lean_dec(v_origAllocId_4214_);
                        lean_dec_ref(v_args_4231_);
                        lean_dec_ref(v_i_4229_);
                        if lean_obj_tag(v___x_4287_) == 0 {
                            v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
                            lean_inc(v_a_4288_);
                            lean_dec_ref_known(v___x_4287_, 1);
                            v___x_4289_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(
                                v___x_4274_,
                                v_decl_4222_,
                                v_a_4218_,
                            );
                            lean_dec_ref(v_decl_4222_);
                            if lean_obj_tag(v___x_4289_) == 0 {
                                lean_dec_ref_known(v___x_4289_, 1);
                                v___x_4290_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4_once), _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4);
                                v___x_4291_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_isSharedId_4215_, v___x_4290_, v_currentRetType_4216_, v_a_4286_, v_a_4288_);
                                if lean_obj_tag(v___x_4291_) == 0 {
                                    v_a_4292_ = lean_ctor_get(v___x_4291_, 0);
                                    v_isSharedCheck_4302_ = (!lean_is_exclusive(v___x_4291_)) as u8;
                                    if v_isSharedCheck_4302_ == 0 {
                                        v___x_4294_ = v___x_4291_;
                                        v_isShared_4295_ = v_isSharedCheck_4302_;
                                        state = 9;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4292_);
                                        lean_dec(v___x_4291_);
                                        v___x_4294_ = lean_box(0);
                                        v_isShared_4295_ = v_isSharedCheck_4302_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_4283_);
                                    lean_del_object(v___x_4261_);
                                    return v___x_4291_;
                                }
                            } else {
                                lean_dec(v_a_4288_);
                                lean_dec(v_a_4286_);
                                lean_dec(v_a_4283_);
                                lean_del_object(v___x_4261_);
                                lean_dec_ref(v_currentRetType_4216_);
                                lean_dec(v_isSharedId_4215_);
                                v_a_4303_ = lean_ctor_get(v___x_4289_, 0);
                                v_isSharedCheck_4310_ = (!lean_is_exclusive(v___x_4289_)) as u8;
                                if v_isSharedCheck_4310_ == 0 {
                                    v___x_4305_ = v___x_4289_;
                                    v_isShared_4306_ = v_isSharedCheck_4310_;
                                    state = 12;
                                    continue;
                                } else {
                                    lean_inc(v_a_4303_);
                                    lean_dec(v___x_4289_);
                                    v___x_4305_ = lean_box(0);
                                    v_isShared_4306_ = v_isSharedCheck_4310_;
                                    state = 12;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_4286_);
                            lean_dec(v_a_4283_);
                            lean_del_object(v___x_4261_);
                            lean_dec_ref(v_decl_4222_);
                            lean_dec_ref(v_currentRetType_4216_);
                            lean_dec(v_isSharedId_4215_);
                            return v___x_4287_;
                        }
                    } else {
                        lean_dec(v_a_4283_);
                        lean_del_object(v___x_4261_);
                        lean_dec_ref(v_args_4231_);
                        lean_dec_ref(v_i_4229_);
                        lean_dec_ref(v_decl_4222_);
                        lean_dec_ref(v_currentRetType_4216_);
                        lean_dec(v_isSharedId_4215_);
                        lean_dec(v_origAllocId_4214_);
                        lean_dec(v_resetTokenId_4212_);
                        return v___x_4285_;
                    }
                } else {
                    lean_dec(v_fst_4269_);
                    lean_del_object(v___x_4261_);
                    lean_dec_ref(v_args_4231_);
                    lean_dec_ref(v_i_4229_);
                    lean_dec_ref(v_decl_4222_);
                    lean_dec_ref(v_currentRetType_4216_);
                    lean_dec(v_isSharedId_4215_);
                    lean_dec(v_origAllocId_4214_);
                    lean_dec(v_resetTokenId_4212_);
                    v_a_4311_ = lean_ctor_get(v___x_4282_, 0);
                    v_isSharedCheck_4318_ = (!lean_is_exclusive(v___x_4282_)) as u8;
                    if v_isSharedCheck_4318_ == 0 {
                        v___x_4313_ = v___x_4282_;
                        v_isShared_4314_ = v_isSharedCheck_4318_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_4311_);
                        lean_dec(v___x_4282_);
                        v___x_4313_ = lean_box(0);
                        v_isShared_4314_ = v_isSharedCheck_4318_;
                        state = 14;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_4262_ == 0 {
                    lean_ctor_set_tag(v___x_4261_, 2);
                    lean_ctor_set(v___x_4261_, 1, v_a_4292_);
                    lean_ctor_set(v___x_4261_, 0, v_a_4283_);
                    v___x_4297_ = v___x_4261_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4301_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4301_, 0, v_a_4283_);
                    lean_ctor_set(v_reuseFailAlloc_4301_, 1, v_a_4292_);
                    v___x_4297_ = v_reuseFailAlloc_4301_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_4295_ == 0 {
                    lean_ctor_set(v___x_4294_, 0, v___x_4297_);
                    v___x_4299_ = v___x_4294_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4300_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4300_, 0, v___x_4297_);
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
                    v_reuseFailAlloc_4309_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4309_, 0, v_a_4303_);
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
                    v_reuseFailAlloc_4317_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4317_, 0, v_a_4311_);
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
                    v_reuseFailAlloc_4326_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_a_4320_);
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
                    v_reuseFailAlloc_4334_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4334_, 0, v_a_4328_);
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
                    v_reuseFailAlloc_4342_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_a_4336_);
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
                    lean_inc_ref(v_decl_4222_);
                    v_isSharedCheck_4366_ = (!lean_is_exclusive(v_code_4213_)) as u8;
                    if v_isSharedCheck_4366_ == 0 {
                        v_unused_4367_ = lean_ctor_get(v_code_4213_, 1);
                        lean_dec(v_unused_4367_);
                        v_unused_4368_ = lean_ctor_get(v_code_4213_, 0);
                        lean_dec(v_unused_4368_);
                        v___x_4358_ = v_code_4213_;
                        v_isShared_4359_ = v_isSharedCheck_4366_;
                        state = 23;
                        continue;
                    } else {
                        lean_dec(v_code_4213_);
                        v___x_4358_ = lean_box(0);
                        v_isShared_4359_ = v_isSharedCheck_4366_;
                        state = 23;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4350_);
                    if v_isShared_4353_ == 0 {
                        lean_ctor_set(v___x_4352_, 0, v_code_4213_);
                        v___x_4370_ = v___x_4352_;
                        state = 26;
                        continue;
                    } else {
                        v_reuseFailAlloc_4371_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4371_, 0, v_code_4213_);
                        v___x_4370_ = v_reuseFailAlloc_4371_;
                        state = 26;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_4359_ == 0 {
                    lean_ctor_set(v___x_4358_, 1, v_a_4350_);
                    v___x_4361_ = v___x_4358_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4365_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_decl_4222_);
                    lean_ctor_set(v_reuseFailAlloc_4365_, 1, v_a_4350_);
                    v___x_4361_ = v_reuseFailAlloc_4365_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                if v_isShared_4353_ == 0 {
                    lean_ctor_set(v___x_4352_, 0, v___x_4361_);
                    v___x_4363_ = v___x_4352_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_4364_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4364_, 0, v___x_4361_);
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
                    v_isSharedCheck_4399_ = (!lean_is_exclusive(v_code_4213_)) as u8;
                    if v_isSharedCheck_4399_ == 0 {
                        v_unused_4400_ = lean_ctor_get(v_code_4213_, 1);
                        lean_dec(v_unused_4400_);
                        v_unused_4401_ = lean_ctor_get(v_code_4213_, 0);
                        lean_dec(v_unused_4401_);
                        v___x_4391_ = v_code_4213_;
                        v_isShared_4392_ = v_isSharedCheck_4399_;
                        state = 29;
                        continue;
                    } else {
                        lean_dec(v_code_4213_);
                        v___x_4391_ = lean_box(0);
                        v_isShared_4392_ = v_isSharedCheck_4399_;
                        state = 29;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4384_);
                    lean_dec(v_a_4382_);
                    if v_isShared_4387_ == 0 {
                        lean_ctor_set(v___x_4386_, 0, v_code_4213_);
                        v___x_4403_ = v___x_4386_;
                        state = 32;
                        continue;
                    } else {
                        v_reuseFailAlloc_4404_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4404_, 0, v_code_4213_);
                        v___x_4403_ = v_reuseFailAlloc_4404_;
                        state = 32;
                        continue;
                    }
                }
            }
            29 => {
                if v_isShared_4392_ == 0 {
                    lean_ctor_set(v___x_4391_, 1, v_a_4384_);
                    lean_ctor_set(v___x_4391_, 0, v_a_4382_);
                    v___x_4394_ = v___x_4391_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_4398_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4398_, 0, v_a_4382_);
                    lean_ctor_set(v_reuseFailAlloc_4398_, 1, v_a_4384_);
                    v___x_4394_ = v_reuseFailAlloc_4398_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                if v_isShared_4387_ == 0 {
                    lean_ctor_set(v___x_4386_, 0, v___x_4394_);
                    v___x_4396_ = v___x_4386_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_4397_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4397_, 0, v___x_4394_);
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
                    v_reuseFailAlloc_4418_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_a_4412_);
                    v___x_4417_ = v_reuseFailAlloc_4418_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_4417_;
            }
            35 => {
                v___x_4428_ = lean_unsigned_to_nat(0);
                lean_inc_ref(v_alts_4424_);
                lean_inc_ref(v_resultType_4422_);
                v___x_4429_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(v_resetTokenId_4212_, v_origAllocId_4214_, v_isSharedId_4215_, v_resultType_4422_, v___x_4428_, v_alts_4424_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                if lean_obj_tag(v___x_4429_) == 0 {
                    v_a_4430_ = lean_ctor_get(v___x_4429_, 0);
                    v_isSharedCheck_4454_ = (!lean_is_exclusive(v___x_4429_)) as u8;
                    if v_isSharedCheck_4454_ == 0 {
                        v___x_4432_ = v___x_4429_;
                        v_isShared_4433_ = v_isSharedCheck_4454_;
                        state = 36;
                        continue;
                    } else {
                        lean_inc(v_a_4430_);
                        lean_dec(v___x_4429_);
                        v___x_4432_ = lean_box(0);
                        v_isShared_4433_ = v_isSharedCheck_4454_;
                        state = 36;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4426_);
                    lean_dec_ref(v_alts_4424_);
                    lean_dec(v_discr_4423_);
                    lean_dec_ref(v_resultType_4422_);
                    lean_dec(v_typeName_4421_);
                    lean_dec_ref_known(v_code_4213_, 1);
                    v_a_4455_ = lean_ctor_get(v___x_4429_, 0);
                    v_isSharedCheck_4462_ = (!lean_is_exclusive(v___x_4429_)) as u8;
                    if v_isSharedCheck_4462_ == 0 {
                        v___x_4457_ = v___x_4429_;
                        v_isShared_4458_ = v_isSharedCheck_4462_;
                        state = 42;
                        continue;
                    } else {
                        lean_inc(v_a_4455_);
                        lean_dec(v___x_4429_);
                        v___x_4457_ = lean_box(0);
                        v_isShared_4458_ = v_isSharedCheck_4462_;
                        state = 42;
                        continue;
                    }
                }
            }
            36 => {
                v___x_4434_ = lean_ptr_addr(v_alts_4424_);
                lean_dec_ref(v_alts_4424_);
                v___x_4435_ = lean_ptr_addr(v_a_4430_);
                v___x_4436_ = lean_usize_dec_eq(v___x_4434_, v___x_4435_);
                if v___x_4436_ == 0 {
                    v_isSharedCheck_4449_ = (!lean_is_exclusive(v_code_4213_)) as u8;
                    if v_isSharedCheck_4449_ == 0 {
                        v_unused_4450_ = lean_ctor_get(v_code_4213_, 0);
                        lean_dec(v_unused_4450_);
                        v___x_4438_ = v_code_4213_;
                        v_isShared_4439_ = v_isSharedCheck_4449_;
                        state = 37;
                        continue;
                    } else {
                        lean_dec(v_code_4213_);
                        v___x_4438_ = lean_box(0);
                        v_isShared_4439_ = v_isSharedCheck_4449_;
                        state = 37;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4430_);
                    lean_del_object(v___x_4426_);
                    lean_dec(v_discr_4423_);
                    lean_dec_ref(v_resultType_4422_);
                    lean_dec(v_typeName_4421_);
                    if v_isShared_4433_ == 0 {
                        lean_ctor_set(v___x_4432_, 0, v_code_4213_);
                        v___x_4452_ = v___x_4432_;
                        state = 41;
                        continue;
                    } else {
                        v_reuseFailAlloc_4453_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_code_4213_);
                        v___x_4452_ = v_reuseFailAlloc_4453_;
                        state = 41;
                        continue;
                    }
                }
            }
            37 => {
                if v_isShared_4427_ == 0 {
                    lean_ctor_set(v___x_4426_, 3, v_a_4430_);
                    v___x_4441_ = v___x_4426_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_4448_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4448_, 0, v_typeName_4421_);
                    lean_ctor_set(v_reuseFailAlloc_4448_, 1, v_resultType_4422_);
                    lean_ctor_set(v_reuseFailAlloc_4448_, 2, v_discr_4423_);
                    lean_ctor_set(v_reuseFailAlloc_4448_, 3, v_a_4430_);
                    v___x_4441_ = v_reuseFailAlloc_4448_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                if v_isShared_4439_ == 0 {
                    lean_ctor_set(v___x_4438_, 0, v___x_4441_);
                    v___x_4443_ = v___x_4438_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_4447_ = lean_alloc_ctor(4, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4447_, 0, v___x_4441_);
                    v___x_4443_ = v_reuseFailAlloc_4447_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                if v_isShared_4433_ == 0 {
                    lean_ctor_set(v___x_4432_, 0, v___x_4443_);
                    v___x_4445_ = v___x_4432_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_4446_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4446_, 0, v___x_4443_);
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
                    v_reuseFailAlloc_4461_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4461_, 0, v_a_4455_);
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
                    lean_inc(v_y_4466_);
                    lean_inc(v_i_4465_);
                    lean_inc(v_fvarId_4464_);
                    v_isSharedCheck_4485_ = (!lean_is_exclusive(v_code_4213_)) as u8;
                    if v_isSharedCheck_4485_ == 0 {
                        v_unused_4486_ = lean_ctor_get(v_code_4213_, 3);
                        lean_dec(v_unused_4486_);
                        v_unused_4487_ = lean_ctor_get(v_code_4213_, 2);
                        lean_dec(v_unused_4487_);
                        v_unused_4488_ = lean_ctor_get(v_code_4213_, 1);
                        lean_dec(v_unused_4488_);
                        v_unused_4489_ = lean_ctor_get(v_code_4213_, 0);
                        lean_dec(v_unused_4489_);
                        v___x_4477_ = v_code_4213_;
                        v_isShared_4478_ = v_isSharedCheck_4485_;
                        state = 45;
                        continue;
                    } else {
                        lean_dec(v_code_4213_);
                        v___x_4477_ = lean_box(0);
                        v_isShared_4478_ = v_isSharedCheck_4485_;
                        state = 45;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4469_);
                    if v_isShared_4472_ == 0 {
                        lean_ctor_set(v___x_4471_, 0, v_code_4213_);
                        v___x_4491_ = v___x_4471_;
                        state = 48;
                        continue;
                    } else {
                        v_reuseFailAlloc_4492_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4492_, 0, v_code_4213_);
                        v___x_4491_ = v_reuseFailAlloc_4492_;
                        state = 48;
                        continue;
                    }
                }
            }
            45 => {
                if v_isShared_4478_ == 0 {
                    lean_ctor_set(v___x_4477_, 3, v_a_4469_);
                    v___x_4480_ = v___x_4477_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_4484_ = lean_alloc_ctor(7, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_fvarId_4464_);
                    lean_ctor_set(v_reuseFailAlloc_4484_, 1, v_i_4465_);
                    lean_ctor_set(v_reuseFailAlloc_4484_, 2, v_y_4466_);
                    lean_ctor_set(v_reuseFailAlloc_4484_, 3, v_a_4469_);
                    v___x_4480_ = v_reuseFailAlloc_4484_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                if v_isShared_4472_ == 0 {
                    lean_ctor_set(v___x_4471_, 0, v___x_4480_);
                    v___x_4482_ = v___x_4471_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_4483_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4483_, 0, v___x_4480_);
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
                    lean_inc(v_y_4496_);
                    lean_inc(v_i_4495_);
                    lean_inc(v_fvarId_4494_);
                    v_isSharedCheck_4515_ = (!lean_is_exclusive(v_code_4213_)) as u8;
                    if v_isSharedCheck_4515_ == 0 {
                        v_unused_4516_ = lean_ctor_get(v_code_4213_, 3);
                        lean_dec(v_unused_4516_);
                        v_unused_4517_ = lean_ctor_get(v_code_4213_, 2);
                        lean_dec(v_unused_4517_);
                        v_unused_4518_ = lean_ctor_get(v_code_4213_, 1);
                        lean_dec(v_unused_4518_);
                        v_unused_4519_ = lean_ctor_get(v_code_4213_, 0);
                        lean_dec(v_unused_4519_);
                        v___x_4507_ = v_code_4213_;
                        v_isShared_4508_ = v_isSharedCheck_4515_;
                        state = 50;
                        continue;
                    } else {
                        lean_dec(v_code_4213_);
                        v___x_4507_ = lean_box(0);
                        v_isShared_4508_ = v_isSharedCheck_4515_;
                        state = 50;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4499_);
                    if v_isShared_4502_ == 0 {
                        lean_ctor_set(v___x_4501_, 0, v_code_4213_);
                        v___x_4521_ = v___x_4501_;
                        state = 53;
                        continue;
                    } else {
                        v_reuseFailAlloc_4522_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4522_, 0, v_code_4213_);
                        v___x_4521_ = v_reuseFailAlloc_4522_;
                        state = 53;
                        continue;
                    }
                }
            }
            50 => {
                if v_isShared_4508_ == 0 {
                    lean_ctor_set(v___x_4507_, 3, v_a_4499_);
                    v___x_4510_ = v___x_4507_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_4514_ = lean_alloc_ctor(8, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_fvarId_4494_);
                    lean_ctor_set(v_reuseFailAlloc_4514_, 1, v_i_4495_);
                    lean_ctor_set(v_reuseFailAlloc_4514_, 2, v_y_4496_);
                    lean_ctor_set(v_reuseFailAlloc_4514_, 3, v_a_4499_);
                    v___x_4510_ = v_reuseFailAlloc_4514_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                if v_isShared_4502_ == 0 {
                    lean_ctor_set(v___x_4501_, 0, v___x_4510_);
                    v___x_4512_ = v___x_4501_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_4513_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4513_, 0, v___x_4510_);
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
                    lean_inc_ref(v_ty_4528_);
                    lean_inc(v_y_4527_);
                    lean_inc(v_offset_4526_);
                    lean_inc(v_i_4525_);
                    lean_inc(v_fvarId_4524_);
                    v_isSharedCheck_4547_ = (!lean_is_exclusive(v_code_4213_)) as u8;
                    if v_isSharedCheck_4547_ == 0 {
                        v_unused_4548_ = lean_ctor_get(v_code_4213_, 5);
                        lean_dec(v_unused_4548_);
                        v_unused_4549_ = lean_ctor_get(v_code_4213_, 4);
                        lean_dec(v_unused_4549_);
                        v_unused_4550_ = lean_ctor_get(v_code_4213_, 3);
                        lean_dec(v_unused_4550_);
                        v_unused_4551_ = lean_ctor_get(v_code_4213_, 2);
                        lean_dec(v_unused_4551_);
                        v_unused_4552_ = lean_ctor_get(v_code_4213_, 1);
                        lean_dec(v_unused_4552_);
                        v_unused_4553_ = lean_ctor_get(v_code_4213_, 0);
                        lean_dec(v_unused_4553_);
                        v___x_4539_ = v_code_4213_;
                        v_isShared_4540_ = v_isSharedCheck_4547_;
                        state = 55;
                        continue;
                    } else {
                        lean_dec(v_code_4213_);
                        v___x_4539_ = lean_box(0);
                        v_isShared_4540_ = v_isSharedCheck_4547_;
                        state = 55;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4531_);
                    if v_isShared_4534_ == 0 {
                        lean_ctor_set(v___x_4533_, 0, v_code_4213_);
                        v___x_4555_ = v___x_4533_;
                        state = 58;
                        continue;
                    } else {
                        v_reuseFailAlloc_4556_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4556_, 0, v_code_4213_);
                        v___x_4555_ = v_reuseFailAlloc_4556_;
                        state = 58;
                        continue;
                    }
                }
            }
            55 => {
                if v_isShared_4540_ == 0 {
                    lean_ctor_set(v___x_4539_, 5, v_a_4531_);
                    v___x_4542_ = v___x_4539_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_4546_ = lean_alloc_ctor(9, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4546_, 0, v_fvarId_4524_);
                    lean_ctor_set(v_reuseFailAlloc_4546_, 1, v_i_4525_);
                    lean_ctor_set(v_reuseFailAlloc_4546_, 2, v_offset_4526_);
                    lean_ctor_set(v_reuseFailAlloc_4546_, 3, v_y_4527_);
                    lean_ctor_set(v_reuseFailAlloc_4546_, 4, v_ty_4528_);
                    lean_ctor_set(v_reuseFailAlloc_4546_, 5, v_a_4531_);
                    v___x_4542_ = v_reuseFailAlloc_4546_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                if v_isShared_4534_ == 0 {
                    lean_ctor_set(v___x_4533_, 0, v___x_4542_);
                    v___x_4544_ = v___x_4533_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_4545_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4545_, 0, v___x_4542_);
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
                    lean_inc(v_cidx_4559_);
                    lean_inc(v_fvarId_4558_);
                    v_isSharedCheck_4578_ = (!lean_is_exclusive(v_code_4213_)) as u8;
                    if v_isSharedCheck_4578_ == 0 {
                        v_unused_4579_ = lean_ctor_get(v_code_4213_, 2);
                        lean_dec(v_unused_4579_);
                        v_unused_4580_ = lean_ctor_get(v_code_4213_, 1);
                        lean_dec(v_unused_4580_);
                        v_unused_4581_ = lean_ctor_get(v_code_4213_, 0);
                        lean_dec(v_unused_4581_);
                        v___x_4570_ = v_code_4213_;
                        v_isShared_4571_ = v_isSharedCheck_4578_;
                        state = 60;
                        continue;
                    } else {
                        lean_dec(v_code_4213_);
                        v___x_4570_ = lean_box(0);
                        v_isShared_4571_ = v_isSharedCheck_4578_;
                        state = 60;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4562_);
                    if v_isShared_4565_ == 0 {
                        lean_ctor_set(v___x_4564_, 0, v_code_4213_);
                        v___x_4583_ = v___x_4564_;
                        state = 63;
                        continue;
                    } else {
                        v_reuseFailAlloc_4584_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4584_, 0, v_code_4213_);
                        v___x_4583_ = v_reuseFailAlloc_4584_;
                        state = 63;
                        continue;
                    }
                }
            }
            60 => {
                if v_isShared_4571_ == 0 {
                    lean_ctor_set(v___x_4570_, 2, v_a_4562_);
                    v___x_4573_ = v___x_4570_;
                    state = 61;
                    continue;
                } else {
                    v_reuseFailAlloc_4577_ = lean_alloc_ctor(10, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_fvarId_4558_);
                    lean_ctor_set(v_reuseFailAlloc_4577_, 1, v_cidx_4559_);
                    lean_ctor_set(v_reuseFailAlloc_4577_, 2, v_a_4562_);
                    v___x_4573_ = v_reuseFailAlloc_4577_;
                    state = 61;
                    continue;
                }
            }
            61 => {
                if v_isShared_4565_ == 0 {
                    lean_ctor_set(v___x_4564_, 0, v___x_4573_);
                    v___x_4575_ = v___x_4564_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_4576_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4576_, 0, v___x_4573_);
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
                    lean_inc(v_n_4587_);
                    lean_inc(v_fvarId_4586_);
                    v_isSharedCheck_4608_ = (!lean_is_exclusive(v_code_4213_)) as u8;
                    if v_isSharedCheck_4608_ == 0 {
                        v_unused_4609_ = lean_ctor_get(v_code_4213_, 2);
                        lean_dec(v_unused_4609_);
                        v_unused_4610_ = lean_ctor_get(v_code_4213_, 1);
                        lean_dec(v_unused_4610_);
                        v_unused_4611_ = lean_ctor_get(v_code_4213_, 0);
                        lean_dec(v_unused_4611_);
                        v___x_4600_ = v_code_4213_;
                        v_isShared_4601_ = v_isSharedCheck_4608_;
                        state = 65;
                        continue;
                    } else {
                        lean_dec(v_code_4213_);
                        v___x_4600_ = lean_box(0);
                        v_isShared_4601_ = v_isSharedCheck_4608_;
                        state = 65;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4592_);
                    if v_isShared_4595_ == 0 {
                        lean_ctor_set(v___x_4594_, 0, v_code_4213_);
                        v___x_4613_ = v___x_4594_;
                        state = 68;
                        continue;
                    } else {
                        v_reuseFailAlloc_4614_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4614_, 0, v_code_4213_);
                        v___x_4613_ = v_reuseFailAlloc_4614_;
                        state = 68;
                        continue;
                    }
                }
            }
            65 => {
                if v_isShared_4601_ == 0 {
                    lean_ctor_set(v___x_4600_, 2, v_a_4592_);
                    v___x_4603_ = v___x_4600_;
                    state = 66;
                    continue;
                } else {
                    v_reuseFailAlloc_4607_ = lean_alloc_ctor(11, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4607_, 0, v_fvarId_4586_);
                    lean_ctor_set(v_reuseFailAlloc_4607_, 1, v_n_4587_);
                    lean_ctor_set(v_reuseFailAlloc_4607_, 2, v_a_4592_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4607_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_check_4588_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4607_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_persistent_4589_,
                    );
                    v___x_4603_ = v_reuseFailAlloc_4607_;
                    state = 66;
                    continue;
                }
            }
            66 => {
                if v_isShared_4595_ == 0 {
                    lean_ctor_set(v___x_4594_, 0, v___x_4603_);
                    v___x_4605_ = v___x_4594_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_4606_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4606_, 0, v___x_4603_);
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
                    lean_inc(v_objs_x3f_4620_);
                    lean_inc(v_n_4617_);
                    lean_inc(v_fvarId_4616_);
                    v_isSharedCheck_4640_ = (!lean_is_exclusive(v_code_4213_)) as u8;
                    if v_isSharedCheck_4640_ == 0 {
                        v_unused_4641_ = lean_ctor_get(v_code_4213_, 3);
                        lean_dec(v_unused_4641_);
                        v_unused_4642_ = lean_ctor_get(v_code_4213_, 2);
                        lean_dec(v_unused_4642_);
                        v_unused_4643_ = lean_ctor_get(v_code_4213_, 1);
                        lean_dec(v_unused_4643_);
                        v_unused_4644_ = lean_ctor_get(v_code_4213_, 0);
                        lean_dec(v_unused_4644_);
                        v___x_4632_ = v_code_4213_;
                        v_isShared_4633_ = v_isSharedCheck_4640_;
                        state = 70;
                        continue;
                    } else {
                        lean_dec(v_code_4213_);
                        v___x_4632_ = lean_box(0);
                        v_isShared_4633_ = v_isSharedCheck_4640_;
                        state = 70;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4624_);
                    if v_isShared_4627_ == 0 {
                        lean_ctor_set(v___x_4626_, 0, v_code_4213_);
                        v___x_4646_ = v___x_4626_;
                        state = 73;
                        continue;
                    } else {
                        v_reuseFailAlloc_4647_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4647_, 0, v_code_4213_);
                        v___x_4646_ = v_reuseFailAlloc_4647_;
                        state = 73;
                        continue;
                    }
                }
            }
            70 => {
                if v_isShared_4633_ == 0 {
                    lean_ctor_set(v___x_4632_, 3, v_a_4624_);
                    v___x_4635_ = v___x_4632_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_4639_ = lean_alloc_ctor(12, 4, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4639_, 0, v_fvarId_4616_);
                    lean_ctor_set(v_reuseFailAlloc_4639_, 1, v_n_4617_);
                    lean_ctor_set(v_reuseFailAlloc_4639_, 2, v_objs_x3f_4620_);
                    lean_ctor_set(v_reuseFailAlloc_4639_, 3, v_a_4624_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4639_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_check_4618_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4639_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                        v_persistent_4619_,
                    );
                    v___x_4635_ = v_reuseFailAlloc_4639_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                if v_isShared_4627_ == 0 {
                    lean_ctor_set(v___x_4626_, 0, v___x_4635_);
                    v___x_4637_ = v___x_4626_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_4638_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4638_, 0, v___x_4635_);
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
                    lean_inc(v_fvarId_4655_);
                    v_isSharedCheck_4674_ = (!lean_is_exclusive(v_code_4213_)) as u8;
                    if v_isSharedCheck_4674_ == 0 {
                        v_unused_4675_ = lean_ctor_get(v_code_4213_, 1);
                        lean_dec(v_unused_4675_);
                        v_unused_4676_ = lean_ctor_get(v_code_4213_, 0);
                        lean_dec(v_unused_4676_);
                        v___x_4666_ = v_code_4213_;
                        v_isShared_4667_ = v_isSharedCheck_4674_;
                        state = 75;
                        continue;
                    } else {
                        lean_dec(v_code_4213_);
                        v___x_4666_ = lean_box(0);
                        v_isShared_4667_ = v_isSharedCheck_4674_;
                        state = 75;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4658_);
                    if v_isShared_4661_ == 0 {
                        lean_ctor_set(v___x_4660_, 0, v_code_4213_);
                        v___x_4678_ = v___x_4660_;
                        state = 78;
                        continue;
                    } else {
                        v_reuseFailAlloc_4679_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4679_, 0, v_code_4213_);
                        v___x_4678_ = v_reuseFailAlloc_4679_;
                        state = 78;
                        continue;
                    }
                }
            }
            75 => {
                if v_isShared_4667_ == 0 {
                    lean_ctor_set(v___x_4666_, 1, v_a_4658_);
                    v___x_4669_ = v___x_4666_;
                    state = 76;
                    continue;
                } else {
                    v_reuseFailAlloc_4673_ = lean_alloc_ctor(13, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4673_, 0, v_fvarId_4655_);
                    lean_ctor_set(v_reuseFailAlloc_4673_, 1, v_a_4658_);
                    v___x_4669_ = v_reuseFailAlloc_4673_;
                    state = 76;
                    continue;
                }
            }
            76 => {
                if v_isShared_4661_ == 0 {
                    lean_ctor_set(v___x_4660_, 0, v___x_4669_);
                    v___x_4671_ = v___x_4660_;
                    state = 77;
                    continue;
                } else {
                    v_reuseFailAlloc_4672_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4672_, 0, v___x_4669_);
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
    mut v_resetTokenId_4682_: *mut LeanObject,
    mut v_origAllocId_4683_: *mut LeanObject,
    mut v_isSharedId_4684_: *mut LeanObject,
    mut v_resultType_4685_: *mut LeanObject,
    mut v_x_4686_: *mut LeanObject,
    mut v___y_4687_: *mut LeanObject,
    mut v___y_4688_: *mut LeanObject,
    mut v___y_4689_: *mut LeanObject,
    mut v___y_4690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4692_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_resetTokenId_4693_: *mut LeanObject,
    mut v_origAllocId_4694_: *mut LeanObject,
    mut v_isSharedId_4695_: *mut LeanObject,
    mut v_resultType_4696_: *mut LeanObject,
    mut v_i_4697_: *mut LeanObject,
    mut v_as_4698_: *mut LeanObject,
    mut v___y_4699_: *mut LeanObject,
    mut v___y_4700_: *mut LeanObject,
    mut v___y_4701_: *mut LeanObject,
    mut v___y_4702_: *mut LeanObject,
    mut v___y_4703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4704_: *mut LeanObject = core::ptr::null_mut();
    v_res_4704_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(v_resetTokenId_4693_, v_origAllocId_4694_, v_isSharedId_4695_, v_resultType_4696_, v_i_4697_, v_as_4698_, v___y_4699_, v___y_4700_, v___y_4701_, v___y_4702_);
    lean_dec(v___y_4702_);
    lean_dec_ref(v___y_4701_);
    lean_dec(v___y_4700_);
    lean_dec_ref(v___y_4699_);
    return v_res_4704_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___boxed(
    mut v_resetTokenId_4705_: *mut LeanObject,
    mut v_code_4706_: *mut LeanObject,
    mut v_origAllocId_4707_: *mut LeanObject,
    mut v_isSharedId_4708_: *mut LeanObject,
    mut v_currentRetType_4709_: *mut LeanObject,
    mut v_a_4710_: *mut LeanObject,
    mut v_a_4711_: *mut LeanObject,
    mut v_a_4712_: *mut LeanObject,
    mut v_a_4713_: *mut LeanObject,
    mut v_a_4714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4715_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4713_);
    lean_dec_ref(v_a_4712_);
    lean_dec(v_a_4711_);
    lean_dec_ref(v_a_4710_);
    return v_res_4715_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(
    mut v_currentRetType_4725_: *mut LeanObject,
    mut v_ds_4726_: *mut LeanObject,
    mut v_decl_4727_: *mut LeanObject,
    mut v_nFields_4728_: *mut LeanObject,
    mut v_origAllocId_4729_: *mut LeanObject,
    mut v_k_4730_: *mut LeanObject,
    mut v_a_4731_: *mut LeanObject,
    mut v_a_4732_: *mut LeanObject,
    mut v_a_4733_: *mut LeanObject,
    mut v_a_4734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4742_: u8 = 0;
    let mut v___x_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: u8 = 0;
    let mut v___x_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: u8 = 0;
    let mut v___x_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_4752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4761_: u8 = 0;
    let mut v___x_4762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4791_: u8 = 0;
    let mut v___x_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4800_: u8 = 0;
    let mut v_unused_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4805_: u8 = 0;
    let mut v___x_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4809_: u8 = 0;
    let mut v_a_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4813_: u8 = 0;
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4817_: u8 = 0;
    let mut v_reuseFailAlloc_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4822_: u8 = 0;
    let mut v___x_4824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4826_: u8 = 0;
    let mut v_a_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4830_: u8 = 0;
    let mut v___x_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4834_: u8 = 0;
    let mut v_a_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4838_: u8 = 0;
    let mut v___x_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4842_: u8 = 0;
    let mut v_isSharedCheck_4843_: u8 = 0;
    let mut v_a_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4847_: u8 = 0;
    let mut v___x_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4851_: u8 = 0;
    let mut v_a_4852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4855_: u8 = 0;
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4859_: u8 = 0;
    let mut v_isSharedCheck_4860_: u8 = 0;
    let mut v_a_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4864_: u8 = 0;
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4868_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4736_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(v_nFields_4728_, v_origAllocId_4729_, v_ds_4726_, v_a_4731_, v_a_4732_, v_a_4733_, v_a_4734_);
                if lean_obj_tag(v___x_4736_) == 0 {
                    v_a_4737_ = lean_ctor_get(v___x_4736_, 0);
                    lean_inc(v_a_4737_);
                    lean_dec_ref_known(v___x_4736_, 1);
                    v_fst_4738_ = lean_ctor_get(v_a_4737_, 0);
                    v_snd_4739_ = lean_ctor_get(v_a_4737_, 1);
                    v_isSharedCheck_4860_ = (!lean_is_exclusive(v_a_4737_)) as u8;
                    if v_isSharedCheck_4860_ == 0 {
                        v___x_4741_ = v_a_4737_;
                        v_isShared_4742_ = v_isSharedCheck_4860_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4739_);
                        lean_inc(v_fst_4738_);
                        lean_dec(v_a_4737_);
                        v___x_4741_ = lean_box(0);
                        v_isShared_4742_ = v_isSharedCheck_4860_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_k_4730_);
                    lean_dec(v_origAllocId_4729_);
                    lean_dec_ref(v_decl_4727_);
                    lean_dec_ref(v_currentRetType_4725_);
                    v_a_4861_ = lean_ctor_get(v___x_4736_, 0);
                    v_isSharedCheck_4868_ = (!lean_is_exclusive(v___x_4736_)) as u8;
                    if v_isSharedCheck_4868_ == 0 {
                        v___x_4863_ = v___x_4736_;
                        v_isShared_4864_ = v_isSharedCheck_4868_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_a_4861_);
                        lean_dec(v___x_4736_);
                        v___x_4863_ = lean_box(0);
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
                if lean_obj_tag(v___x_4744_) == 0 {
                    v_a_4745_ = lean_ctor_get(v___x_4744_, 0);
                    lean_inc(v_a_4745_);
                    lean_dec_ref_known(v___x_4744_, 1);
                    v___x_4746_ = 1;
                    v___x_4747_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4_once), _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4);
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
                    if lean_obj_tag(v___x_4749_) == 0 {
                        v_a_4750_ = lean_ctor_get(v___x_4749_, 0);
                        lean_inc(v_a_4750_);
                        lean_dec_ref_known(v___x_4749_, 1);
                        v_fvarId_4751_ = lean_ctor_get(v_decl_4727_, 0);
                        v_binderName_4752_ = lean_ctor_get(v_decl_4727_, 1);
                        v_fvarId_4753_ = lean_ctor_get(v_a_4750_, 0);
                        lean_inc_ref(v_currentRetType_4725_);
                        lean_inc(v_fvarId_4753_);
                        lean_inc(v_origAllocId_4729_);
                        lean_inc(v_fvarId_4751_);
                        v___x_4754_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_fvarId_4751_, v_k_4730_, v_origAllocId_4729_, v_fvarId_4753_, v_currentRetType_4725_, v_a_4731_, v_a_4732_, v_a_4733_, v_a_4734_);
                        if lean_obj_tag(v___x_4754_) == 0 {
                            v_a_4755_ = lean_ctor_get(v___x_4754_, 0);
                            lean_inc(v_a_4755_);
                            lean_dec_ref_known(v___x_4754_, 1);
                            v___x_4756_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0;
                            lean_inc_ref(v_currentRetType_4725_);
                            v___x_4757_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_a_4755_, v___x_4756_, v_currentRetType_4725_, v_a_4731_, v_a_4732_, v_a_4733_, v_a_4734_);
                            if lean_obj_tag(v___x_4757_) == 0 {
                                v_a_4758_ = lean_ctor_get(v___x_4757_, 0);
                                v_isSharedCheck_4843_ = (!lean_is_exclusive(v___x_4757_)) as u8;
                                if v_isSharedCheck_4843_ == 0 {
                                    v___x_4760_ = v___x_4757_;
                                    v_isShared_4761_ = v_isSharedCheck_4843_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_4758_);
                                    lean_dec(v___x_4757_);
                                    v___x_4760_ = lean_box(0);
                                    v_isShared_4761_ = v_isSharedCheck_4843_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_4750_);
                                lean_del_object(v___x_4741_);
                                lean_dec(v_snd_4739_);
                                lean_dec(v_fst_4738_);
                                lean_dec(v_origAllocId_4729_);
                                lean_dec_ref(v_decl_4727_);
                                lean_dec_ref(v_currentRetType_4725_);
                                return v___x_4757_;
                            }
                        } else {
                            lean_dec(v_a_4750_);
                            lean_del_object(v___x_4741_);
                            lean_dec(v_snd_4739_);
                            lean_dec(v_fst_4738_);
                            lean_dec(v_origAllocId_4729_);
                            lean_dec_ref(v_decl_4727_);
                            lean_dec_ref(v_currentRetType_4725_);
                            return v___x_4754_;
                        }
                    } else {
                        lean_del_object(v___x_4741_);
                        lean_dec(v_snd_4739_);
                        lean_dec(v_fst_4738_);
                        lean_dec_ref(v_k_4730_);
                        lean_dec(v_origAllocId_4729_);
                        lean_dec_ref(v_decl_4727_);
                        lean_dec_ref(v_currentRetType_4725_);
                        v_a_4844_ = lean_ctor_get(v___x_4749_, 0);
                        v_isSharedCheck_4851_ = (!lean_is_exclusive(v___x_4749_)) as u8;
                        if v_isSharedCheck_4851_ == 0 {
                            v___x_4846_ = v___x_4749_;
                            v_isShared_4847_ = v_isSharedCheck_4851_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_4844_);
                            lean_dec(v___x_4749_);
                            v___x_4846_ = lean_box(0);
                            v_isShared_4847_ = v_isSharedCheck_4851_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4741_);
                    lean_dec(v_snd_4739_);
                    lean_dec(v_fst_4738_);
                    lean_dec_ref(v_k_4730_);
                    lean_dec(v_origAllocId_4729_);
                    lean_dec_ref(v_decl_4727_);
                    lean_dec_ref(v_currentRetType_4725_);
                    v_a_4852_ = lean_ctor_get(v___x_4744_, 0);
                    v_isSharedCheck_4859_ = (!lean_is_exclusive(v___x_4744_)) as u8;
                    if v_isSharedCheck_4859_ == 0 {
                        v___x_4854_ = v___x_4744_;
                        v_isShared_4855_ = v_isSharedCheck_4859_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_4852_);
                        lean_dec(v___x_4744_);
                        v___x_4854_ = lean_box(0);
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
                if lean_obj_tag(v___x_4763_) == 0 {
                    v_a_4764_ = lean_ctor_get(v___x_4763_, 0);
                    lean_inc(v_a_4764_);
                    lean_dec_ref_known(v___x_4763_, 1);
                    v___x_4765_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4);
                    lean_inc(v_binderName_4752_);
                    lean_inc(v_fvarId_4751_);
                    v___x_4766_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v___x_4766_, 0, v_fvarId_4751_);
                    lean_ctor_set(v___x_4766_, 1, v_binderName_4752_);
                    lean_ctor_set(v___x_4766_, 2, v___x_4765_);
                    lean_ctor_set_uint8(
                        v___x_4766_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v___x_4748_,
                    );
                    v___x_4767_ = lean_unsigned_to_nat(2);
                    v___x_4768_ = lean_mk_empty_array_with_capacity(v___x_4767_);
                    v___x_4769_ = lean_array_push(v___x_4768_, v___x_4766_);
                    v___x_4770_ = lean_array_push(v___x_4769_, v_a_4750_);
                    lean_inc_ref(v_currentRetType_4725_);
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
                    if lean_obj_tag(v___x_4771_) == 0 {
                        v_a_4772_ = lean_ctor_get(v___x_4771_, 0);
                        lean_inc(v_a_4772_);
                        lean_dec_ref_known(v___x_4771_, 1);
                        v___x_4773_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__5;
                        v___x_4774_ =
                            l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_4773_, v_a_4732_);
                        if lean_obj_tag(v___x_4774_) == 0 {
                            v_a_4775_ = lean_ctor_get(v___x_4774_, 0);
                            lean_inc(v_a_4775_);
                            lean_dec_ref_known(v___x_4774_, 1);
                            lean_inc(v_origAllocId_4729_);
                            if v_isShared_4761_ == 0 {
                                lean_ctor_set_tag(v___x_4760_, 15);
                                lean_ctor_set(v___x_4760_, 0, v_origAllocId_4729_);
                                v___x_4777_ = v___x_4760_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_4818_ = lean_alloc_ctor(15, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4818_, 0, v_origAllocId_4729_);
                                v___x_4777_ = v_reuseFailAlloc_4818_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4772_);
                            lean_del_object(v___x_4760_);
                            lean_del_object(v___x_4741_);
                            lean_dec(v_snd_4739_);
                            lean_dec(v_fst_4738_);
                            lean_dec(v_origAllocId_4729_);
                            lean_dec_ref(v_decl_4727_);
                            lean_dec_ref(v_currentRetType_4725_);
                            v_a_4819_ = lean_ctor_get(v___x_4774_, 0);
                            v_isSharedCheck_4826_ = (!lean_is_exclusive(v___x_4774_)) as u8;
                            if v_isSharedCheck_4826_ == 0 {
                                v___x_4821_ = v___x_4774_;
                                v_isShared_4822_ = v_isSharedCheck_4826_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_a_4819_);
                                lean_dec(v___x_4774_);
                                v___x_4821_ = lean_box(0);
                                v_isShared_4822_ = v_isSharedCheck_4826_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_4760_);
                        lean_del_object(v___x_4741_);
                        lean_dec(v_snd_4739_);
                        lean_dec(v_fst_4738_);
                        lean_dec(v_origAllocId_4729_);
                        lean_dec_ref(v_decl_4727_);
                        lean_dec_ref(v_currentRetType_4725_);
                        v_a_4827_ = lean_ctor_get(v___x_4771_, 0);
                        v_isSharedCheck_4834_ = (!lean_is_exclusive(v___x_4771_)) as u8;
                        if v_isSharedCheck_4834_ == 0 {
                            v___x_4829_ = v___x_4771_;
                            v_isShared_4830_ = v_isSharedCheck_4834_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_4827_);
                            lean_dec(v___x_4771_);
                            v___x_4829_ = lean_box(0);
                            v_isShared_4830_ = v_isSharedCheck_4834_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4760_);
                    lean_dec(v_a_4758_);
                    lean_dec(v_a_4750_);
                    lean_del_object(v___x_4741_);
                    lean_dec(v_snd_4739_);
                    lean_dec(v_fst_4738_);
                    lean_dec(v_origAllocId_4729_);
                    lean_dec_ref(v_decl_4727_);
                    lean_dec_ref(v_currentRetType_4725_);
                    v_a_4835_ = lean_ctor_get(v___x_4763_, 0);
                    v_isSharedCheck_4842_ = (!lean_is_exclusive(v___x_4763_)) as u8;
                    if v_isSharedCheck_4842_ == 0 {
                        v___x_4837_ = v___x_4763_;
                        v_isShared_4838_ = v_isSharedCheck_4842_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_4835_);
                        lean_dec(v___x_4763_);
                        v___x_4837_ = lean_box(0);
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
                if lean_obj_tag(v___x_4778_) == 0 {
                    v_a_4779_ = lean_ctor_get(v___x_4778_, 0);
                    lean_inc(v_a_4779_);
                    lean_dec_ref_known(v___x_4778_, 1);
                    v_fvarId_4780_ = lean_ctor_get(v_a_4772_, 0);
                    v_fvarId_4781_ = lean_ctor_get(v_a_4779_, 0);
                    lean_inc(v_fvarId_4781_);
                    lean_inc(v_fvarId_4780_);
                    lean_inc(v_origAllocId_4729_);
                    v___x_4782_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(v_origAllocId_4729_, v_snd_4739_, v_fvarId_4780_, v_fvarId_4781_, v_a_4731_, v_a_4732_, v_a_4733_, v_a_4734_);
                    if lean_obj_tag(v___x_4782_) == 0 {
                        v_a_4783_ = lean_ctor_get(v___x_4782_, 0);
                        lean_inc(v_a_4783_);
                        lean_dec_ref_known(v___x_4782_, 1);
                        lean_inc(v_fvarId_4781_);
                        lean_inc(v_fvarId_4780_);
                        v___x_4784_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(v_origAllocId_4729_, v_snd_4739_, v_fvarId_4780_, v_fvarId_4781_, v_a_4731_, v_a_4732_, v_a_4733_, v_a_4734_);
                        lean_dec(v_snd_4739_);
                        if lean_obj_tag(v___x_4784_) == 0 {
                            v_a_4785_ = lean_ctor_get(v___x_4784_, 0);
                            lean_inc(v_a_4785_);
                            lean_dec_ref_known(v___x_4784_, 1);
                            lean_inc(v_fvarId_4781_);
                            v___x_4786_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_fvarId_4781_, v___x_4747_, v_currentRetType_4725_, v_a_4783_, v_a_4785_);
                            if lean_obj_tag(v___x_4786_) == 0 {
                                v_a_4787_ = lean_ctor_get(v___x_4786_, 0);
                                lean_inc(v_a_4787_);
                                lean_dec_ref_known(v___x_4786_, 1);
                                v___x_4788_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(
                                    v___x_4746_,
                                    v_decl_4727_,
                                    v_a_4732_,
                                );
                                lean_dec_ref(v_decl_4727_);
                                if lean_obj_tag(v___x_4788_) == 0 {
                                    v_isSharedCheck_4800_ = (!lean_is_exclusive(v___x_4788_)) as u8;
                                    if v_isSharedCheck_4800_ == 0 {
                                        v_unused_4801_ = lean_ctor_get(v___x_4788_, 0);
                                        lean_dec(v_unused_4801_);
                                        v___x_4790_ = v___x_4788_;
                                        v_isShared_4791_ = v_isSharedCheck_4800_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_dec(v___x_4788_);
                                        v___x_4790_ = lean_box(0);
                                        v_isShared_4791_ = v_isSharedCheck_4800_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_4787_);
                                    lean_dec(v_a_4779_);
                                    lean_dec(v_a_4772_);
                                    lean_del_object(v___x_4741_);
                                    lean_dec(v_fst_4738_);
                                    v_a_4802_ = lean_ctor_get(v___x_4788_, 0);
                                    v_isSharedCheck_4809_ = (!lean_is_exclusive(v___x_4788_)) as u8;
                                    if v_isSharedCheck_4809_ == 0 {
                                        v___x_4804_ = v___x_4788_;
                                        v_isShared_4805_ = v_isSharedCheck_4809_;
                                        state = 7;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4802_);
                                        lean_dec(v___x_4788_);
                                        v___x_4804_ = lean_box(0);
                                        v_isShared_4805_ = v_isSharedCheck_4809_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_4779_);
                                lean_dec(v_a_4772_);
                                lean_del_object(v___x_4741_);
                                lean_dec(v_fst_4738_);
                                lean_dec_ref(v_decl_4727_);
                                return v___x_4786_;
                            }
                        } else {
                            lean_dec(v_a_4783_);
                            lean_dec(v_a_4779_);
                            lean_dec(v_a_4772_);
                            lean_del_object(v___x_4741_);
                            lean_dec(v_fst_4738_);
                            lean_dec_ref(v_decl_4727_);
                            lean_dec_ref(v_currentRetType_4725_);
                            return v___x_4784_;
                        }
                    } else {
                        lean_dec(v_a_4779_);
                        lean_dec(v_a_4772_);
                        lean_del_object(v___x_4741_);
                        lean_dec(v_snd_4739_);
                        lean_dec(v_fst_4738_);
                        lean_dec(v_origAllocId_4729_);
                        lean_dec_ref(v_decl_4727_);
                        lean_dec_ref(v_currentRetType_4725_);
                        return v___x_4782_;
                    }
                } else {
                    lean_dec(v_a_4772_);
                    lean_del_object(v___x_4741_);
                    lean_dec(v_snd_4739_);
                    lean_dec(v_fst_4738_);
                    lean_dec(v_origAllocId_4729_);
                    lean_dec_ref(v_decl_4727_);
                    lean_dec_ref(v_currentRetType_4725_);
                    v_a_4810_ = lean_ctor_get(v___x_4778_, 0);
                    v_isSharedCheck_4817_ = (!lean_is_exclusive(v___x_4778_)) as u8;
                    if v_isSharedCheck_4817_ == 0 {
                        v___x_4812_ = v___x_4778_;
                        v_isShared_4813_ = v_isSharedCheck_4817_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_4810_);
                        lean_dec(v___x_4778_);
                        v___x_4812_ = lean_box(0);
                        v_isShared_4813_ = v_isSharedCheck_4817_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4742_ == 0 {
                    lean_ctor_set(v___x_4741_, 1, v_a_4787_);
                    lean_ctor_set(v___x_4741_, 0, v_a_4779_);
                    v___x_4793_ = v___x_4741_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4799_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_a_4779_);
                    lean_ctor_set(v_reuseFailAlloc_4799_, 1, v_a_4787_);
                    v___x_4793_ = v_reuseFailAlloc_4799_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4794_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4794_, 0, v_a_4772_);
                lean_ctor_set(v___x_4794_, 1, v___x_4793_);
                v___x_4795_ =
                    l_Lean_Compiler_LCNF_attachCodeDecls(v___x_4746_, v_fst_4738_, v___x_4794_);
                lean_dec(v_fst_4738_);
                if v_isShared_4791_ == 0 {
                    lean_ctor_set(v___x_4790_, 0, v___x_4795_);
                    v___x_4797_ = v___x_4790_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4798_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4798_, 0, v___x_4795_);
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
                    v_reuseFailAlloc_4808_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4808_, 0, v_a_4802_);
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
                    v_reuseFailAlloc_4816_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4816_, 0, v_a_4810_);
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
                    v_reuseFailAlloc_4825_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4825_, 0, v_a_4819_);
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
                    v_reuseFailAlloc_4833_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4833_, 0, v_a_4827_);
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
                    v_reuseFailAlloc_4841_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4841_, 0, v_a_4835_);
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
                    v_reuseFailAlloc_4850_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4850_, 0, v_a_4844_);
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
                    v_reuseFailAlloc_4858_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4858_, 0, v_a_4852_);
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
                    v_reuseFailAlloc_4867_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4867_, 0, v_a_4861_);
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
    mut v_resultType_4869_: *mut LeanObject,
    mut v_x_4870_: *mut LeanObject,
    mut v___y_4871_: *mut LeanObject,
    mut v___y_4872_: *mut LeanObject,
    mut v___y_4873_: *mut LeanObject,
    mut v___y_4874_: *mut LeanObject,
    mut v___y_4875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4876_: *mut LeanObject = core::ptr::null_mut();
    v_res_4876_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0(v_resultType_4869_, v_x_4870_, v___y_4871_, v___y_4872_, v___y_4873_, v___y_4874_);
    lean_dec(v___y_4874_);
    lean_dec_ref(v___y_4873_);
    lean_dec(v___y_4872_);
    lean_dec_ref(v___y_4871_);
    return v_res_4876_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(
    mut v_resultType_4877_: *mut LeanObject,
    mut v_i_4878_: *mut LeanObject,
    mut v_as_4879_: *mut LeanObject,
    mut v___y_4880_: *mut LeanObject,
    mut v___y_4881_: *mut LeanObject,
    mut v___y_4882_: *mut LeanObject,
    mut v___y_4883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: u8 = 0;
    let mut v___x_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: usize = 0;
    let mut v___x_4893_: usize = 0;
    let mut v___x_4894_: u8 = 0;
    let mut v___x_4895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4905_: u8 = 0;
    let mut v___x_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4909_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4885_ = lean_array_get_size(v_as_4879_);
                v___x_4886_ = lean_nat_dec_lt(v_i_4878_, v___x_4885_);
                if v___x_4886_ == 0 {
                    lean_dec(v_i_4878_);
                    lean_dec_ref(v_resultType_4877_);
                    v___x_4887_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4887_, 0, v_as_4879_);
                    return v___x_4887_;
                } else {
                    lean_inc_ref(v_resultType_4877_);
                    v___f_4888_ = lean_alloc_closure(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                    lean_closure_set(v___f_4888_, 0, v_resultType_4877_);
                    v_a_4889_ = lean_array_fget_borrowed(v_as_4879_, v_i_4878_);
                    lean_inc(v_a_4889_);
                    v___x_4890_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_a_4889_, v___f_4888_, v___y_4880_, v___y_4881_, v___y_4882_, v___y_4883_);
                    if lean_obj_tag(v___x_4890_) == 0 {
                        v_a_4891_ = lean_ctor_get(v___x_4890_, 0);
                        lean_inc(v_a_4891_);
                        lean_dec_ref_known(v___x_4890_, 1);
                        v___x_4892_ = lean_ptr_addr(v_a_4889_);
                        v___x_4893_ = lean_ptr_addr(v_a_4891_);
                        v___x_4894_ = lean_usize_dec_eq(v___x_4892_, v___x_4893_);
                        if v___x_4894_ == 0 {
                            v___x_4895_ = lean_unsigned_to_nat(1);
                            v___x_4896_ = lean_nat_add(v_i_4878_, v___x_4895_);
                            v___x_4897_ = lean_array_fset(v_as_4879_, v_i_4878_, v_a_4891_);
                            lean_dec(v_i_4878_);
                            v_i_4878_ = v___x_4896_;
                            v_as_4879_ = v___x_4897_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_a_4891_);
                            v___x_4899_ = lean_unsigned_to_nat(1);
                            v___x_4900_ = lean_nat_add(v_i_4878_, v___x_4899_);
                            lean_dec(v_i_4878_);
                            v_i_4878_ = v___x_4900_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_as_4879_);
                        lean_dec(v_i_4878_);
                        lean_dec_ref(v_resultType_4877_);
                        v_a_4902_ = lean_ctor_get(v___x_4890_, 0);
                        v_isSharedCheck_4909_ = (!lean_is_exclusive(v___x_4890_)) as u8;
                        if v_isSharedCheck_4909_ == 0 {
                            v___x_4904_ = v___x_4890_;
                            v_isShared_4905_ = v_isSharedCheck_4909_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4902_);
                            lean_dec(v___x_4890_);
                            v___x_4904_ = lean_box(0);
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
                    v_reuseFailAlloc_4908_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4908_, 0, v_a_4902_);
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
    mut v_code_4910_: *mut LeanObject,
    mut v_ds_4911_: *mut LeanObject,
    mut v_currentRetType_4912_: *mut LeanObject,
    mut v_a_4913_: *mut LeanObject,
    mut v_a_4914_: *mut LeanObject,
    mut v_a_4915_: *mut LeanObject,
    mut v_a_4916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_code_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ds_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: u8 = 0;
    let mut v_d_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_4933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4947_: u8 = 0;
    let mut v___x_4948_: u8 = 0;
    let mut v___x_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4959_: u8 = 0;
    let mut v___x_4961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4963_: u8 = 0;
    let mut v_isSharedCheck_4964_: u8 = 0;
    let mut v_cases_4965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_resultType_4967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discr_4968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_4969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4972_: u8 = 0;
    let mut v___x_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4978_: u8 = 0;
    let mut v___x_4979_: u8 = 0;
    let mut v___y_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: usize = 0;
    let mut v___x_4987_: usize = 0;
    let mut v___x_4988_: u8 = 0;
    let mut v___x_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4991_: u8 = 0;
    let mut v___x_4993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4998_: u8 = 0;
    let mut v_unused_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5000_: u8 = 0;
    let mut v_a_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5004_: u8 = 0;
    let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5008_: u8 = 0;
    let mut v_isSharedCheck_5009_: u8 = 0;
    let mut v_k_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: u8 = 0;
    let mut v___x_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_code_4910_) {
                0 => {
                    v_decl_4930_ = lean_ctor_get(v_code_4910_, 0);
                    v_value_4931_ = lean_ctor_get(v_decl_4930_, 3);
                    if lean_obj_tag(v_value_4931_) == 11 {
                        lean_inc_ref(v_decl_4930_);
                        v_k_4932_ = lean_ctor_get(v_code_4910_, 1);
                        lean_inc_ref(v_k_4932_);
                        lean_dec_ref_known(v_code_4910_, 2);
                        v_n_4933_ = lean_ctor_get(v_value_4931_, 0);
                        lean_inc(v_n_4933_);
                        v_var_4934_ = lean_ctor_get(v_value_4931_, 1);
                        lean_inc(v_var_4934_);
                        v___x_4935_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(v_currentRetType_4912_, v_ds_4911_, v_decl_4930_, v_n_4933_, v_var_4934_, v_k_4932_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_);
                        return v___x_4935_;
                    } else {
                        v_k_4936_ = lean_ctor_get(v_code_4910_, 1);
                        lean_inc_ref(v_k_4936_);
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
                    v_decl_4937_ = lean_ctor_get(v_code_4910_, 0);
                    lean_inc_ref(v_decl_4937_);
                    v_k_4938_ = lean_ctor_get(v_code_4910_, 1);
                    lean_inc_ref(v_k_4938_);
                    lean_dec_ref_known(v_code_4910_, 2);
                    v_params_4939_ = lean_ctor_get(v_decl_4937_, 2);
                    lean_inc_ref(v_params_4939_);
                    v_type_4940_ = lean_ctor_get(v_decl_4937_, 3);
                    lean_inc_ref_n(v_type_4940_, 2);
                    v_value_4941_ = lean_ctor_get(v_decl_4937_, 4);
                    v___x_4942_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0;
                    lean_inc_ref(v_value_4941_);
                    v___x_4943_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_value_4941_, v___x_4942_, v_type_4940_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_);
                    if lean_obj_tag(v___x_4943_) == 0 {
                        v_a_4944_ = lean_ctor_get(v___x_4943_, 0);
                        v_isSharedCheck_4964_ = (!lean_is_exclusive(v___x_4943_)) as u8;
                        if v_isSharedCheck_4964_ == 0 {
                            v___x_4946_ = v___x_4943_;
                            v_isShared_4947_ = v_isSharedCheck_4964_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_4944_);
                            lean_dec(v___x_4943_);
                            v___x_4946_ = lean_box(0);
                            v_isShared_4947_ = v_isSharedCheck_4964_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_type_4940_);
                        lean_dec_ref(v_params_4939_);
                        lean_dec_ref(v_k_4938_);
                        lean_dec_ref(v_decl_4937_);
                        lean_dec_ref(v_currentRetType_4912_);
                        lean_dec_ref(v_ds_4911_);
                        return v___x_4943_;
                    }
                }
                4 => {
                    lean_dec_ref(v_currentRetType_4912_);
                    v_cases_4965_ = lean_ctor_get(v_code_4910_, 0);
                    lean_inc_ref(v_cases_4965_);
                    v_typeName_4966_ = lean_ctor_get(v_cases_4965_, 0);
                    v_resultType_4967_ = lean_ctor_get(v_cases_4965_, 1);
                    v_discr_4968_ = lean_ctor_get(v_cases_4965_, 2);
                    v_alts_4969_ = lean_ctor_get(v_cases_4965_, 3);
                    v_isSharedCheck_5009_ = (!lean_is_exclusive(v_cases_4965_)) as u8;
                    if v_isSharedCheck_5009_ == 0 {
                        v___x_4971_ = v_cases_4965_;
                        v_isShared_4972_ = v_isSharedCheck_5009_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_alts_4969_);
                        lean_inc(v_discr_4968_);
                        lean_inc(v_resultType_4967_);
                        lean_inc(v_typeName_4966_);
                        lean_dec(v_cases_4965_);
                        v___x_4971_ = lean_box(0);
                        v_isShared_4972_ = v_isSharedCheck_5009_;
                        state = 6;
                        continue;
                    }
                }
                7 => {
                    v_k_5010_ = lean_ctor_get(v_code_4910_, 3);
                    lean_inc_ref(v_k_5010_);
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
                    v_k_5011_ = lean_ctor_get(v_code_4910_, 3);
                    lean_inc_ref(v_k_5011_);
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
                    v_k_5012_ = lean_ctor_get(v_code_4910_, 5);
                    lean_inc_ref(v_k_5012_);
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
                    v_k_5013_ = lean_ctor_get(v_code_4910_, 2);
                    lean_inc_ref(v_k_5013_);
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
                    v_k_5014_ = lean_ctor_get(v_code_4910_, 2);
                    lean_inc_ref(v_k_5014_);
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
                    v_k_5015_ = lean_ctor_get(v_code_4910_, 3);
                    lean_inc_ref(v_k_5015_);
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
                    v_k_5016_ = lean_ctor_get(v_code_4910_, 1);
                    lean_inc_ref(v_k_5016_);
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
                    lean_dec_ref(v_currentRetType_4912_);
                    v___x_5017_ = 1;
                    v___x_5018_ =
                        l_Lean_Compiler_LCNF_attachCodeDecls(v___x_5017_, v_ds_4911_, v_code_4910_);
                    lean_dec_ref(v_ds_4911_);
                    v___x_5019_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5019_, 0, v___x_5018_);
                    return v___x_5019_;
                }
            },
            1 => {
                v___x_4926_ = 1;
                v_d_4927_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_4926_, v_code_4919_);
                lean_dec_ref(v_code_4919_);
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
                if lean_obj_tag(v___x_4949_) == 0 {
                    v_a_4950_ = lean_ctor_get(v___x_4949_, 0);
                    lean_inc(v_a_4950_);
                    lean_dec_ref_known(v___x_4949_, 1);
                    if v_isShared_4947_ == 0 {
                        lean_ctor_set_tag(v___x_4946_, 2);
                        lean_ctor_set(v___x_4946_, 0, v_a_4950_);
                        v___x_4952_ = v___x_4946_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4955_ = lean_alloc_ctor(2, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4955_, 0, v_a_4950_);
                        v___x_4952_ = v_reuseFailAlloc_4955_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4946_);
                    lean_dec_ref(v_k_4938_);
                    lean_dec_ref(v_currentRetType_4912_);
                    lean_dec_ref(v_ds_4911_);
                    v_a_4956_ = lean_ctor_get(v___x_4949_, 0);
                    v_isSharedCheck_4963_ = (!lean_is_exclusive(v___x_4949_)) as u8;
                    if v_isSharedCheck_4963_ == 0 {
                        v___x_4958_ = v___x_4949_;
                        v_isShared_4959_ = v_isSharedCheck_4963_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4956_);
                        lean_dec(v___x_4949_);
                        v___x_4958_ = lean_box(0);
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
                    v_reuseFailAlloc_4962_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4962_, 0, v_a_4956_);
                    v___x_4961_ = v_reuseFailAlloc_4962_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4961_;
            }
            6 => {
                v___x_4973_ = lean_unsigned_to_nat(0);
                lean_inc_ref(v_alts_4969_);
                lean_inc_ref(v_resultType_4967_);
                v___x_4974_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(v_resultType_4967_, v___x_4973_, v_alts_4969_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_);
                if lean_obj_tag(v___x_4974_) == 0 {
                    v_a_4975_ = lean_ctor_get(v___x_4974_, 0);
                    v_isSharedCheck_5000_ = (!lean_is_exclusive(v___x_4974_)) as u8;
                    if v_isSharedCheck_5000_ == 0 {
                        v___x_4977_ = v___x_4974_;
                        v_isShared_4978_ = v_isSharedCheck_5000_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_4975_);
                        lean_dec(v___x_4974_);
                        v___x_4977_ = lean_box(0);
                        v_isShared_4978_ = v_isSharedCheck_5000_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4971_);
                    lean_dec_ref(v_alts_4969_);
                    lean_dec(v_discr_4968_);
                    lean_dec_ref(v_resultType_4967_);
                    lean_dec(v_typeName_4966_);
                    lean_dec_ref_known(v_code_4910_, 1);
                    lean_dec_ref(v_ds_4911_);
                    v_a_5001_ = lean_ctor_get(v___x_4974_, 0);
                    v_isSharedCheck_5008_ = (!lean_is_exclusive(v___x_4974_)) as u8;
                    if v_isSharedCheck_5008_ == 0 {
                        v___x_5003_ = v___x_4974_;
                        v_isShared_5004_ = v_isSharedCheck_5008_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_5001_);
                        lean_dec(v___x_4974_);
                        v___x_5003_ = lean_box(0);
                        v_isShared_5004_ = v_isSharedCheck_5008_;
                        state = 13;
                        continue;
                    }
                }
            }
            7 => {
                v___x_4979_ = 1;
                v___x_4986_ = lean_ptr_addr(v_alts_4969_);
                lean_dec_ref(v_alts_4969_);
                v___x_4987_ = lean_ptr_addr(v_a_4975_);
                v___x_4988_ = lean_usize_dec_eq(v___x_4986_, v___x_4987_);
                if v___x_4988_ == 0 {
                    v_isSharedCheck_4998_ = (!lean_is_exclusive(v_code_4910_)) as u8;
                    if v_isSharedCheck_4998_ == 0 {
                        v_unused_4999_ = lean_ctor_get(v_code_4910_, 0);
                        lean_dec(v_unused_4999_);
                        v___x_4990_ = v_code_4910_;
                        v_isShared_4991_ = v_isSharedCheck_4998_;
                        state = 10;
                        continue;
                    } else {
                        lean_dec(v_code_4910_);
                        v___x_4990_ = lean_box(0);
                        v_isShared_4991_ = v_isSharedCheck_4998_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4975_);
                    lean_del_object(v___x_4971_);
                    lean_dec(v_discr_4968_);
                    lean_dec_ref(v_resultType_4967_);
                    lean_dec(v_typeName_4966_);
                    v___y_4981_ = v_code_4910_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4982_ =
                    l_Lean_Compiler_LCNF_attachCodeDecls(v___x_4979_, v_ds_4911_, v___y_4981_);
                lean_dec_ref(v_ds_4911_);
                if v_isShared_4978_ == 0 {
                    lean_ctor_set(v___x_4977_, 0, v___x_4982_);
                    v___x_4984_ = v___x_4977_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4985_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4985_, 0, v___x_4982_);
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
                    lean_ctor_set(v___x_4971_, 3, v_a_4975_);
                    v___x_4993_ = v___x_4971_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4997_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4997_, 0, v_typeName_4966_);
                    lean_ctor_set(v_reuseFailAlloc_4997_, 1, v_resultType_4967_);
                    lean_ctor_set(v_reuseFailAlloc_4997_, 2, v_discr_4968_);
                    lean_ctor_set(v_reuseFailAlloc_4997_, 3, v_a_4975_);
                    v___x_4993_ = v_reuseFailAlloc_4997_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_4991_ == 0 {
                    lean_ctor_set(v___x_4990_, 0, v___x_4993_);
                    v___x_4995_ = v___x_4990_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4996_ = lean_alloc_ctor(4, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4996_, 0, v___x_4993_);
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
                    v_reuseFailAlloc_5007_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5007_, 0, v_a_5001_);
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
    mut v_resultType_5020_: *mut LeanObject,
    mut v_x_5021_: *mut LeanObject,
    mut v___y_5022_: *mut LeanObject,
    mut v___y_5023_: *mut LeanObject,
    mut v___y_5024_: *mut LeanObject,
    mut v___y_5025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_resultType_5029_: *mut LeanObject,
    mut v_i_5030_: *mut LeanObject,
    mut v_as_5031_: *mut LeanObject,
    mut v___y_5032_: *mut LeanObject,
    mut v___y_5033_: *mut LeanObject,
    mut v___y_5034_: *mut LeanObject,
    mut v___y_5035_: *mut LeanObject,
    mut v___y_5036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5037_: *mut LeanObject = core::ptr::null_mut();
    v_res_5037_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(v_resultType_5029_, v_i_5030_, v_as_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_);
    lean_dec(v___y_5035_);
    lean_dec_ref(v___y_5034_);
    lean_dec(v___y_5033_);
    lean_dec_ref(v___y_5032_);
    return v_res_5037_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse___boxed(
    mut v_code_5038_: *mut LeanObject,
    mut v_ds_5039_: *mut LeanObject,
    mut v_currentRetType_5040_: *mut LeanObject,
    mut v_a_5041_: *mut LeanObject,
    mut v_a_5042_: *mut LeanObject,
    mut v_a_5043_: *mut LeanObject,
    mut v_a_5044_: *mut LeanObject,
    mut v_a_5045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5046_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5044_);
    lean_dec_ref(v_a_5043_);
    lean_dec(v_a_5042_);
    lean_dec_ref(v_a_5041_);
    return v_res_5046_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___boxed(
    mut v_currentRetType_5047_: *mut LeanObject,
    mut v_ds_5048_: *mut LeanObject,
    mut v_decl_5049_: *mut LeanObject,
    mut v_nFields_5050_: *mut LeanObject,
    mut v_origAllocId_5051_: *mut LeanObject,
    mut v_k_5052_: *mut LeanObject,
    mut v_a_5053_: *mut LeanObject,
    mut v_a_5054_: *mut LeanObject,
    mut v_a_5055_: *mut LeanObject,
    mut v_a_5056_: *mut LeanObject,
    mut v_a_5057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5058_: *mut LeanObject = core::ptr::null_mut();
    v_res_5058_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(v_currentRetType_5047_, v_ds_5048_, v_decl_5049_, v_nFields_5050_, v_origAllocId_5051_, v_k_5052_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_);
    lean_dec(v_a_5056_);
    lean_dec_ref(v_a_5055_);
    lean_dec(v_a_5054_);
    lean_dec_ref(v_a_5053_);
    return v_res_5058_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(
    mut v_f_5059_: *mut LeanObject,
    mut v_v_5060_: *mut LeanObject,
    mut v___y_5061_: *mut LeanObject,
    mut v___y_5062_: *mut LeanObject,
    mut v___y_5063_: *mut LeanObject,
    mut v___y_5064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_code_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5069_: u8 = 0;
    let mut v___x_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5074_: u8 = 0;
    let mut v___x_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5081_: u8 = 0;
    let mut v_a_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5085_: u8 = 0;
    let mut v___x_5087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5089_: u8 = 0;
    let mut v_isSharedCheck_5090_: u8 = 0;
    let mut v___x_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_5060_) == 0 {
                    v_code_5066_ = lean_ctor_get(v_v_5060_, 0);
                    v_isSharedCheck_5090_ = (!lean_is_exclusive(v_v_5060_)) as u8;
                    if v_isSharedCheck_5090_ == 0 {
                        v___x_5068_ = v_v_5060_;
                        v_isShared_5069_ = v_isSharedCheck_5090_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_code_5066_);
                        lean_dec(v_v_5060_);
                        v___x_5068_ = lean_box(0);
                        v_isShared_5069_ = v_isSharedCheck_5090_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_f_5059_);
                    v___x_5091_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5091_, 0, v_v_5060_);
                    return v___x_5091_;
                }
            }
            1 => {
                lean_inc(v___y_5064_);
                lean_inc_ref(v___y_5063_);
                lean_inc(v___y_5062_);
                lean_inc_ref(v___y_5061_);
                v___x_5070_ = lean_apply_6(
                    v_f_5059_,
                    v_code_5066_,
                    v___y_5061_,
                    v___y_5062_,
                    v___y_5063_,
                    v___y_5064_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_5070_) == 0 {
                    v_a_5071_ = lean_ctor_get(v___x_5070_, 0);
                    v_isSharedCheck_5081_ = (!lean_is_exclusive(v___x_5070_)) as u8;
                    if v_isSharedCheck_5081_ == 0 {
                        v___x_5073_ = v___x_5070_;
                        v_isShared_5074_ = v_isSharedCheck_5081_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5071_);
                        lean_dec(v___x_5070_);
                        v___x_5073_ = lean_box(0);
                        v_isShared_5074_ = v_isSharedCheck_5081_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5068_);
                    v_a_5082_ = lean_ctor_get(v___x_5070_, 0);
                    v_isSharedCheck_5089_ = (!lean_is_exclusive(v___x_5070_)) as u8;
                    if v_isSharedCheck_5089_ == 0 {
                        v___x_5084_ = v___x_5070_;
                        v_isShared_5085_ = v_isSharedCheck_5089_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5082_);
                        lean_dec(v___x_5070_);
                        v___x_5084_ = lean_box(0);
                        v_isShared_5085_ = v_isSharedCheck_5089_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5069_ == 0 {
                    lean_ctor_set(v___x_5068_, 0, v_a_5071_);
                    v___x_5076_ = v___x_5068_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5080_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5080_, 0, v_a_5071_);
                    v___x_5076_ = v_reuseFailAlloc_5080_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5074_ == 0 {
                    lean_ctor_set(v___x_5073_, 0, v___x_5076_);
                    v___x_5078_ = v___x_5073_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5079_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5079_, 0, v___x_5076_);
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
                    v_reuseFailAlloc_5088_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5088_, 0, v_a_5082_);
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
    mut v_f_5092_: *mut LeanObject,
    mut v_v_5093_: *mut LeanObject,
    mut v___y_5094_: *mut LeanObject,
    mut v___y_5095_: *mut LeanObject,
    mut v___y_5096_: *mut LeanObject,
    mut v___y_5097_: *mut LeanObject,
    mut v___y_5098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5099_: *mut LeanObject = core::ptr::null_mut();
    v_res_5099_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v_f_5092_, v_v_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_);
    lean_dec(v___y_5097_);
    lean_dec_ref(v___y_5096_);
    lean_dec(v___y_5095_);
    lean_dec_ref(v___y_5094_);
    return v_res_5099_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0(
    mut v_pu_5100_: u8,
    mut v_f_5101_: *mut LeanObject,
    mut v_v_5102_: *mut LeanObject,
    mut v___y_5103_: *mut LeanObject,
    mut v___y_5104_: *mut LeanObject,
    mut v___y_5105_: *mut LeanObject,
    mut v___y_5106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5108_: *mut LeanObject = core::ptr::null_mut();
    v___x_5108_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v_f_5101_, v_v_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_);
    return v___x_5108_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___boxed(
    mut v_pu_5109_: *mut LeanObject,
    mut v_f_5110_: *mut LeanObject,
    mut v_v_5111_: *mut LeanObject,
    mut v___y_5112_: *mut LeanObject,
    mut v___y_5113_: *mut LeanObject,
    mut v___y_5114_: *mut LeanObject,
    mut v___y_5115_: *mut LeanObject,
    mut v___y_5116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5117_: u8 = 0;
    let mut v_res_5118_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5117_ = (lean_unbox(v_pu_5109_) as u8);
    v_res_5118_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0(v_pu_boxed_5117_, v_f_5110_, v_v_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_);
    lean_dec(v___y_5115_);
    lean_dec_ref(v___y_5114_);
    lean_dec(v___y_5113_);
    lean_dec_ref(v___y_5112_);
    return v_res_5118_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0(
    mut v_toSignature_5119_: *mut LeanObject,
    mut v_x_5120_: *mut LeanObject,
    mut v___y_5121_: *mut LeanObject,
    mut v___y_5122_: *mut LeanObject,
    mut v___y_5123_: *mut LeanObject,
    mut v___y_5124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_type_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
    v_type_5126_ = lean_ctor_get(v_toSignature_5119_, 2);
    lean_inc_ref(v_type_5126_);
    lean_dec_ref(v_toSignature_5119_);
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
    mut v_toSignature_5129_: *mut LeanObject,
    mut v_x_5130_: *mut LeanObject,
    mut v___y_5131_: *mut LeanObject,
    mut v___y_5132_: *mut LeanObject,
    mut v___y_5133_: *mut LeanObject,
    mut v___y_5134_: *mut LeanObject,
    mut v___y_5135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5136_: *mut LeanObject = core::ptr::null_mut();
    v_res_5136_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0(v_toSignature_5129_, v_x_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_);
    lean_dec(v___y_5134_);
    lean_dec_ref(v___y_5133_);
    lean_dec(v___y_5132_);
    lean_dec_ref(v___y_5131_);
    return v_res_5136_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse(
    mut v_decl_5137_: *mut LeanObject,
    mut v_a_5138_: *mut LeanObject,
    mut v_a_5139_: *mut LeanObject,
    mut v_a_5140_: *mut LeanObject,
    mut v_a_5141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5147_: u8 = 0;
    let mut v_resetReuse_5148_: u8 = 0;
    let mut v___x_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recursive_5154_: u8 = 0;
    let mut v_inlineAttr_x3f_5155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5158_: u8 = 0;
    let mut v___f_5159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5164_: u8 = 0;
    let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5171_: u8 = 0;
    let mut v_a_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5175_: u8 = 0;
    let mut v___x_5177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5179_: u8 = 0;
    let mut v_isSharedCheck_5180_: u8 = 0;
    let mut v_isSharedCheck_5181_: u8 = 0;
    let mut v_a_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5185_: u8 = 0;
    let mut v___x_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5189_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5143_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_5138_);
                if lean_obj_tag(v___x_5143_) == 0 {
                    v_a_5144_ = lean_ctor_get(v___x_5143_, 0);
                    v_isSharedCheck_5181_ = (!lean_is_exclusive(v___x_5143_)) as u8;
                    if v_isSharedCheck_5181_ == 0 {
                        v___x_5146_ = v___x_5143_;
                        v_isShared_5147_ = v_isSharedCheck_5181_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5144_);
                        lean_dec(v___x_5143_);
                        v___x_5146_ = lean_box(0);
                        v_isShared_5147_ = v_isSharedCheck_5181_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_decl_5137_);
                    v_a_5182_ = lean_ctor_get(v___x_5143_, 0);
                    v_isSharedCheck_5189_ = (!lean_is_exclusive(v___x_5143_)) as u8;
                    if v_isSharedCheck_5189_ == 0 {
                        v___x_5184_ = v___x_5143_;
                        v_isShared_5185_ = v_isSharedCheck_5189_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_5182_);
                        lean_dec(v___x_5143_);
                        v___x_5184_ = lean_box(0);
                        v_isShared_5185_ = v_isSharedCheck_5189_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_resetReuse_5148_ = lean_ctor_get_uint8(
                    v_a_5144_,
                    (core::mem::size_of::<*mut LeanObject>() * 4 + 2) as u32,
                );
                lean_dec(v_a_5144_);
                if v_resetReuse_5148_ == 0 {
                    if v_isShared_5147_ == 0 {
                        lean_ctor_set(v___x_5146_, 0, v_decl_5137_);
                        v___x_5150_ = v___x_5146_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5151_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5151_, 0, v_decl_5137_);
                        v___x_5150_ = v_reuseFailAlloc_5151_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5146_);
                    v_toSignature_5152_ = lean_ctor_get(v_decl_5137_, 0);
                    v_value_5153_ = lean_ctor_get(v_decl_5137_, 1);
                    v_recursive_5154_ = lean_ctor_get_uint8(
                        v_decl_5137_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_inlineAttr_x3f_5155_ = lean_ctor_get(v_decl_5137_, 2);
                    v_isSharedCheck_5180_ = (!lean_is_exclusive(v_decl_5137_)) as u8;
                    if v_isSharedCheck_5180_ == 0 {
                        v___x_5157_ = v_decl_5137_;
                        v_isShared_5158_ = v_isSharedCheck_5180_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_inlineAttr_x3f_5155_);
                        lean_inc(v_value_5153_);
                        lean_inc(v_toSignature_5152_);
                        lean_dec(v_decl_5137_);
                        v___x_5157_ = lean_box(0);
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
                lean_inc_ref(v_toSignature_5152_);
                v___f_5159_ = lean_alloc_closure(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                lean_closure_set(v___f_5159_, 0, v_toSignature_5152_);
                v___x_5160_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v___f_5159_, v_value_5153_, v_a_5138_, v_a_5139_, v_a_5140_, v_a_5141_);
                if lean_obj_tag(v___x_5160_) == 0 {
                    v_a_5161_ = lean_ctor_get(v___x_5160_, 0);
                    v_isSharedCheck_5171_ = (!lean_is_exclusive(v___x_5160_)) as u8;
                    if v_isSharedCheck_5171_ == 0 {
                        v___x_5163_ = v___x_5160_;
                        v_isShared_5164_ = v_isSharedCheck_5171_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_5161_);
                        lean_dec(v___x_5160_);
                        v___x_5163_ = lean_box(0);
                        v_isShared_5164_ = v_isSharedCheck_5171_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5157_);
                    lean_dec(v_inlineAttr_x3f_5155_);
                    lean_dec_ref(v_toSignature_5152_);
                    v_a_5172_ = lean_ctor_get(v___x_5160_, 0);
                    v_isSharedCheck_5179_ = (!lean_is_exclusive(v___x_5160_)) as u8;
                    if v_isSharedCheck_5179_ == 0 {
                        v___x_5174_ = v___x_5160_;
                        v_isShared_5175_ = v_isSharedCheck_5179_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_5172_);
                        lean_dec(v___x_5160_);
                        v___x_5174_ = lean_box(0);
                        v_isShared_5175_ = v_isSharedCheck_5179_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_5158_ == 0 {
                    lean_ctor_set(v___x_5157_, 1, v_a_5161_);
                    v___x_5166_ = v___x_5157_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5170_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5170_, 0, v_toSignature_5152_);
                    lean_ctor_set(v_reuseFailAlloc_5170_, 1, v_a_5161_);
                    lean_ctor_set(v_reuseFailAlloc_5170_, 2, v_inlineAttr_x3f_5155_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5170_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_recursive_5154_,
                    );
                    v___x_5166_ = v_reuseFailAlloc_5170_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5164_ == 0 {
                    lean_ctor_set(v___x_5163_, 0, v___x_5166_);
                    v___x_5168_ = v___x_5163_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5169_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5169_, 0, v___x_5166_);
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
                    v_reuseFailAlloc_5178_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5178_, 0, v_a_5172_);
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
                    v_reuseFailAlloc_5188_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5188_, 0, v_a_5182_);
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
    mut v_decl_5190_: *mut LeanObject,
    mut v_a_5191_: *mut LeanObject,
    mut v_a_5192_: *mut LeanObject,
    mut v_a_5193_: *mut LeanObject,
    mut v_a_5194_: *mut LeanObject,
    mut v_a_5195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5196_: *mut LeanObject = core::ptr::null_mut();
    v_res_5196_ =
        l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse(
            v_decl_5190_,
            v_a_5191_,
            v_a_5192_,
            v_a_5193_,
            v_a_5194_,
        );
    lean_dec(v_a_5194_);
    lean_dec_ref(v_a_5193_);
    lean_dec(v_a_5192_);
    lean_dec_ref(v_a_5191_);
    return v_res_5196_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_expandResetReuse___closed__3() -> *mut LeanObject {
    let mut v___x_5201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: u8 = 0;
    let mut v___x_5204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: *mut LeanObject = core::ptr::null_mut();
    v___x_5201_ = lean_unsigned_to_nat(0);
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
pub unsafe fn _init_l_Lean_Compiler_LCNF_expandResetReuse() -> *mut LeanObject {
    let mut v___x_5206_: *mut LeanObject = core::ptr::null_mut();
    v___x_5206_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_expandResetReuse___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_expandResetReuse___closed__3_once),
        _init_l_Lean_Compiler_LCNF_expandResetReuse___closed__3,
    );
    return v___x_5206_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut LeanObject = core::ptr::null_mut();
    v___x_5262_ = lean_unsigned_to_nat(2743268278);
    v___x_5263_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_;
    v___x_5264_ = l_Lean_Name_num___override(v___x_5263_, v___x_5262_);
    return v___x_5264_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut LeanObject = core::ptr::null_mut();
    v___x_5266_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_;
    v___x_5267_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
    v___x_5268_ = l_Lean_Name_str___override(v___x_5267_, v___x_5266_);
    return v___x_5268_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_5270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut LeanObject = core::ptr::null_mut();
    v___x_5270_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_;
    v___x_5271_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
    v___x_5272_ = l_Lean_Name_str___override(v___x_5271_, v___x_5270_);
    return v___x_5272_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_5273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut LeanObject = core::ptr::null_mut();
    v___x_5273_ = lean_unsigned_to_nat(2);
    v___x_5274_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
    v___x_5275_ = l_Lean_Name_num___override(v___x_5274_, v___x_5273_);
    return v___x_5275_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_5277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: u8 = 0;
    let mut v___x_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut LeanObject = core::ptr::null_mut();
    v___x_5277_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_;
    v___x_5278_ = 1;
    v___x_5279_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
    v___x_5280_ = l_Lean_registerTraceClass(v___x_5277_, v___x_5278_, v___x_5279_);
    return v___x_5280_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2____boxed(
    mut v_a_5281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5282_: *mut LeanObject = core::ptr::null_mut();
    v_res_5282_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_();
    return v_res_5282_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_ExpandResetReuse(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Compiler_LCNF_expandResetReuse = _init_l_Lean_Compiler_LCNF_expandResetReuse();
    lean_mark_persistent(l_Lean_Compiler_LCNF_expandResetReuse);
    res = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_ExpandResetReuse(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_ExpandResetReuse(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ExpandResetReuse(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_ExpandResetReuse(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_ExpandResetReuse(builtin);
}
